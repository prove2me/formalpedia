-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_separable_purity_tetrahedron
-- name    : QAlgorithms.Papers.Independent.Information100.P19.separable_purity_tetrahedron
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:49:54.618978+00:00
-- url     : https://prove2.me/theorems/36a7f9ef-091f-4b29-91f0-5cd33255e457
-- title:
--   Proposition 4.6
-- statement:
--   Let $K_2$ be the triples $(\pi,\pi_A,\pi_B)$ obtained from separable trace-one states in all positive finite local dimensions, where the entries are the global and marginal purities. Then
--   $$\overline{\operatorname{conv}}(K_2)=\{\pi\ge0,\ \pi_A\ge\pi,\ \pi_B\ge\pi,\ \pi_A+\pi_B\le1+\pi\}.$$
--   This is the tetrahedron with vertices $(0,0,0),(0,1,0),(0,0,1),(1,1,1)$. The closure accounts for vertices obtained only as dimension tends to infinity.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 24, Proposition 4.6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Proposition 4.6; arXiv:2609.29471v1, PDF pp.24, 25. -/
theorem separable_purity_tetrahedron  :
    closure (convexHull ℝ K2) =
      {v | 0 ≤ v 0 ∧ v 0 ≤ v 1 ∧ v 0 ≤ v 2 ∧ v 1+v 2 ≤ 1+v 0} ∧
    closure (convexHull ℝ K2) = convexHull ℝ
      ({![0,0,0],![0,1,0],![0,0,1],![1,1,1]} : Set (Fin 3 → ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
