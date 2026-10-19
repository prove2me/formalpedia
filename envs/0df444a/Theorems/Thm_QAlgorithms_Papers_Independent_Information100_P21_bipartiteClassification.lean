-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_bipartiteClassification
-- name    : QAlgorithms.Papers.Independent.Information100.P21.bipartiteClassification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:13:54.353696+00:00
-- url     : https://prove2.me/theorems/66d78468-6826-4fdf-a12e-980dc37f9c50
-- title:
--   IX.D — complete bipartite classification
-- statement:
--   For positive finite local dimensions $m,n$, using the actual bipartite separable cone,
--   $$[\forall\rho,\ R_s(\rho)=R_g(\rho)]\iff[\min(m,n)=1\ \text{or}\ (m,n)=(2,2)].$$
--   Every other nontrivial pair contains a strict-gap density operator. Its embedding into larger spaces need not be full rank. This combines S155 with the adjacent one-dimensional case.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 3, IX.D — complete bipartite classification

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF p. 3, complete bipartite classification. -/
theorem bipartiteClassification (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
  ((∀ rho : Op (Fin m × Fin n), QAlgorithms.IsDensityMatrix rho → rs rho=rg rho) ↔
    min m n=1 ∨ (m=2 ∧ n=2)) ∧
  (¬(min m n=1 ∨ (m=2 ∧ n=2)) →
    ∃ rho : Op (Fin m × Fin n), QAlgorithms.IsDensityMatrix rho ∧ rg rho<rs rho) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
