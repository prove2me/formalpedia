-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_correlatedInputInformation
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.correlatedInputInformation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:08:25.155899+00:00
-- url     : https://prove2.me/theorems/cdc20035-4fb2-4525-96c3-6aa5f52db9f9
-- title:
--   Corollary A.18: For arbitrary joint classical P(x1,…,xn) and conditional product outputs tensor_k W_k(xk), I(X1…Xn:Y1…Yn)≤sum_k I(Xk:Yk).
-- statement:
--   Let finite classical alphabets $X_k$ carry an arbitrary JOINT probability law $P(x_1,\ldots,x_n)$. Conditional on the tuple, output $\bigotimes_kW_k(x_k)$ on finite intrinsic systems $Y_k$. Every $W_k(x_k)$ is normalized; independence of the classical coordinates is not required. Information is evaluated in this actual cq state.
--
--   $$
--   I(X_1\cdots X_n;Y_1\cdots Y_n)\le\sum_k I(X_k;Y_k).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 74, Corollary A.18

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

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Corollary A.18, PDF p.74. Arbitrary correlated classical P is allowed; only
outputs conditioned on the whole input tuple factor over k. The entropy differences
are the mutual informations of the explicitly given cq channel state. -/
theorem correlatedInputInformation {n : ℕ} (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (Y : Fin n → IntrinsicSystem) (P : PMF (∀ i, Fin (a i)))
    (W : ∀ i, Fin (a i) → Matrix (Fin (Y i).dim) (Fin (Y i).dim) ℂ)
    (hW : ∀ i x, (Y i).IsState (W i x)) :
    vnEntropy (∑ x, ((P x).toReal : ℂ) • wordTensor (fun i => W i (x i))) -
      (∑ x, (P x).toReal * vnEntropy (wordTensor (fun i => W i (x i)))) ≤
    ∑ i, (vnEntropy (∑ x, ((P x).toReal : ℂ) • W i (x i)) -
      ∑ x, (P x).toReal * vnEntropy (W i (x i))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
