-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_comparableSourceSubsets
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.comparableSourceSubsets
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:57:11.158952+00:00
-- url     : https://prove2.me/theorems/7a7b93da-8a59-4000-ab11-6c9a9372d271
-- title:
--   Lemma IV.18: Saturation R(K)=H(X(K)|Y X(Kc)) plus lower subset inequalities only for J⊆K or K⊆J imply all subset inequalities.
-- statement:
--   For any finite correlated classical/hybrid source, write $(J)$ for $R(J)\ge H(X(J)\mid YX(J^c))$, with $R(J)=\sum_{j\in J}R_j$. Let $K$ be any sender subset, including empty or full, and suppose its constraint is saturated.
--
--   $$
--   R(K)=H(X(K)\mid YX(K^c)),\quad (J)\ \text{for }J\subseteq K\text{ or }K\subseteq J\Longrightarrow(J)\ \text{for every }J.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 57, Lemma IV.18

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

/-- Lemma IV.18, PDF pp.57-58: inclusive comparisons with K, including the empty
and full cases. These are lower source bounds, not the channel upper bounds. -/
theorem comparableSourceSubsets {s : ℕ} (S : HybridSource s) (R : Fin s → ℝ)
    (K : Finset (Fin s)) (hsaturated : ∑ i ∈ K, R i = S.subsetEntropy K)
    (hbelow : ∀ J : Finset (Fin s), J ⊆ K → S.subsetEntropy J ≤ ∑ i ∈ J, R i)
    (habove : ∀ J : Finset (Fin s), K ⊆ J → S.subsetEntropy J ≤ ∑ i ∈ J, R i) :
    R ∈ S.lowerRegion := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
