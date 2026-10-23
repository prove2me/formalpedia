-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_sourceExtremePoints
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.sourceExtremePoints
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:57:52.977779+00:00
-- url     : https://prove2.me/theorems/27d26367-d79a-4bd1-a3cb-8ea65737866d
-- title:
--   source-region-extreme-points: Every extreme point of R(J)≥H(X(J)|Y X(Jc)) is a permutation tuple R_pi(i)=H(X_pi(i)|Y X_pi(1)…X_pi(i−1)); every such tuple is fea
-- statement:
--   For a finite correlated classical/hybrid source, consider the upward unbounded region defined by all lower subset constraints $R(J)\ge H(X(J)\mid YX(J^c))$. Extremality is ordinary convex extremality, with no upper-maximality condition.
--
--   $$
--   R\text{ extreme}\Longrightarrow\exists\pi:\ R_{\pi(i)}=H(X_{\pi(i)}\mid YX_{\pi(1)}\cdots X_{\pi(i-1)});\qquad\text{every such tuple is feasible}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 57, source-region-extreme-points

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

/-- Unnumbered source-region extreme-point assertion, PDF pp.57-58: every extreme
point is a permutation corner, and every such corner is feasible. The region is
upward closed and unbounded, unlike a classical-input channel rate polytope. -/
theorem sourceExtremePoints {s : ℕ} (S : HybridSource s) :
    (∀ R : Fin s → ℝ, IsExtreme S.lowerRegion R → ∃ pi, R = S.corner pi) ∧
    (∀ pi : Equiv.Perm (Fin s), S.corner pi ∈ S.lowerRegion) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
