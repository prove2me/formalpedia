-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_psd_cubic_moments
-- name    : QAlgorithms.Papers.Independent.Information100.P19.psd_cubic_moments
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:46:11.405493+00:00
-- url     : https://prove2.me/theorems/3a121c76-41e9-4ee1-a5f3-e84fc57e6547
-- title:
--   Corollary 3.7
-- statement:
--   In dual coordinates $(x,y,z)$ to $([1^3],[21],[3])$, the closed PSD moment cone is
--   $$\{(x,y,z):z\ge0,\ y-z\ge0,\ x-(2k+1)y+k(k+1)z\ge0\text{ for every }k\ge1\}.$$
--   Its slice $x=1$, projected to $(y,z)$, is the closed convex hull of $(0,0)$ and $(1/m,1/m^2)$ for positive integers $m$. This slice is convexified moment data, rather than the raw realization set.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 17, Corollary 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Corollary 3.7; arXiv:2609.29471v1, PDF pp.17, 18. -/
theorem psd_cubic_moments  :
    psdMom 3 = {y | 0 ≤ y ⟨[3],by decide⟩ ∧
      0 ≤ y ⟨[2,1],by decide⟩ - y ⟨[3],by decide⟩ ∧
      ∀ k : ℕ, 1 ≤ k → 0 ≤ y ⟨[1,1,1],by decide⟩ -
        (2*(k:ℝ)+1)*y ⟨[2,1],by decide⟩ + (k:ℝ)*(k+1)*y ⟨[3],by decide⟩} ∧
    {v : Fin 2 → ℝ | ∃ y ∈ psdMom 3, y ⟨[1,1,1],by decide⟩ = 1 ∧
      v = ![y ⟨[2,1],by decide⟩,y ⟨[3],by decide⟩]} =
      closure (convexHull ℝ ({0} ∪ {v | ∃ m : ℕ, 1 ≤ m ∧
        v = ![1/(m:ℝ),1/(m:ℝ)^2]})) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
