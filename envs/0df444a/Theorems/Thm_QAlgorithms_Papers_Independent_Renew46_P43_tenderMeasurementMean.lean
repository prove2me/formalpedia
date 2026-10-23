-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_tenderMeasurementMean
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.tenderMeasurementMean
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:20:00.404345+00:00
-- url     : https://prove2.me/theorems/e9995222-30b6-4a39-b1e5-0e077f25a47f
-- title:
--   Remark I.6: Mean identification error≤lambdaBar implies both mean disturbances from I.5≤sqrt(8lambdaBar)+lambdaBar.
-- statement:
--   Use the states, countable POVM and square-root instruments above, but assume only $\mathbb E_a[1-\operatorname{Tr}(\rho_aD_{\phi(a)})]\le\bar\lambda$, for a discrete probability law on the labels and $\bar\lambda>0$. No pointwise error bound is required.
--
--   $$
--   \mathbb E\|\rho_a-D_{\rm int,*}(\rho_a)\|_1\le\sqrt{8\bar\lambda}+\bar\lambda,\quad\mathbb E\|[\phi(a)]\otimes\rho_a-D_{\rm tot,*}(\rho_a)\|_1\le\sqrt{8\bar\lambda}+\bar\lambda.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 10, Remark I.6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Remark I.6, PDF p.10: the average of norms, under only a mean error bound. -/
theorem tenderMeasurementMean {A B I : Type*} [Countable B] [Fintype I] [DecidableEq I]
    (rho : A → Matrix I I ℂ) (hrho : ∀ a, IsDensityMatrix (rho a))
    (D : B → Matrix I I ℂ) (hD : IsCountablePOVM D) (phi : A → B) (P : PMF A)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (herror : (∑' a, (P a).toReal * (1 - effectProb (rho a) (D (phi a)))) ≤ lambda) :
    (∑' a, (P a).toReal * traceNorm (rho a - interior D (rho a))) ≤
      Real.sqrt (8 * lambda) + lambda ∧
    (∑' a, (P a).toReal * totalDisturbance D (rho a) (phi a)) ≤
      Real.sqrt (8 * lambda) + lambda := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
