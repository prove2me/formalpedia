-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_tenderMeasurement
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.tenderMeasurement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:18:54.834592+00:00
-- url     : https://prove2.me/theorems/535515fd-cb06-4eb6-9d03-35f49f124f2d
-- title:
--   Lemma I.5: If D identifies phi(a) in rho_a with pointwise error≤lambda>0, both ||rho_a−Dint*(rho_a)||1 and ||[phi(a)]⊗rho_a−Dtot*(rho_a)||1 a
-- statement:
--   Let $\rho_a$ be normalized states, let $(D_b)_{b\in B}$ be a finite or countable POVM, and let $\phi:A\to B$. Suppose $\lambda>0$ and $1-\operatorname{Tr}(\rho_aD_{\phi(a)})\le\lambda$ for every $a$. The interior instrument is $D_{\rm int,*}(\rho)=\sum_b\sqrt{D_b}\rho\sqrt{D_b}$; the total instrument retains $b$ as a classical label.
--
--   $$
--   \|\rho_a-D_{\rm int,*}(\rho_a)\|_1\le\sqrt{8\lambda}+\lambda,\qquad \|[\phi(a)]\otimes\rho_a-D_{\rm tot,*}(\rho_a)\|_1\le\sqrt{8\lambda}+\lambda.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 10, Lemma I.5

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

/-- Lemma I.5, PDF p.10; countable observables as permitted on PDF p.62.
The second bound retains the real outcome, rather than replacing the instrument. -/
theorem tenderMeasurement {A B I : Type*} [Countable B] [Fintype I] [DecidableEq I]
    (rho : A → Matrix I I ℂ) (hrho : ∀ a, IsDensityMatrix (rho a))
    (D : B → Matrix I I ℂ) (hD : IsCountablePOVM D) (phi : A → B)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (herror : ∀ a, 1 - effectProb (rho a) (D (phi a)) ≤ lambda) :
    (∀ a, traceNorm (rho a - interior D (rho a)) ≤ Real.sqrt (8 * lambda) + lambda) ∧
    (∀ a, totalDisturbance D (rho a) (phi a) ≤ Real.sqrt (8 * lambda) + lambda) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
