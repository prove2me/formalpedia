-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_induced_positive_attainment
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.induced_positive_attainment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:31:30.968587+00:00
-- url     : https://prove2.me/theorems/0a6254a8-857b-468f-a2b8-65a72103805d
-- title:
--   Corollary 6: induced norm attained at a positive input
-- statement:
--   Let $\Phi:M_m\to M_n$ be CP, with $m,n\ge1$, and let $1\le q,p\le\infty$. The full induced Schatten norm equals its restriction to positive semidefinite matrices, and a positive input attains it:
--
--   $$\|\Phi\|_{q\to p}=\|\Phi\|^+_{q\to p}=\|\Phi(X)\|_p\quad\text{for some }X\ge0\text{ with }\|X\|_q=1.$$
--
--   The endpoint infinity means operator norm. This retains actual attainment in addition to equality of suprema.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 12, Corollary 6: induced norm attained at a positive input

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- Corollary 6, PDF p.12: equality of induced norms and actual positive-input attainment. -/
theorem induced_positive_attainment {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (q p : ℝ≥0∞) (hq : 1 ≤ q) (hp : 1 ≤ p)
    (Phi : (Mat I →ₗ[ℂ] Mat J)) (hPhi : Entanglement.IsCompletelyPositive Phi) :
    inducedSize q p Phi = positiveInducedSize q p Phi ∧
    ∃ X : Mat I, X.PosSemidef ∧ schattenNorm q X = 1 ∧
      inducedSize q p Phi = ENNReal.ofReal (schattenNorm p (Phi X)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
