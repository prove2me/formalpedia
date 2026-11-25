-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_ptsIntegralAt_eq_c05886725c9e
-- name    : P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_ptsIntegralAt_eq_c05886725c9e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:58:31.735797+00:00
-- url     : https://prove2.me/theorems/d0251527-248a-5230-8a4b-767a067be685
-- title:
--   P2 M Ground Theory Heights  Heights Pts Integral Points pts Integral At eq c05886725c9e: P2 M Ground Theory Heights  Heights Pts Integral Points pts Integral At eq c05886725c9e
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Integral Points pts Integral At eq c05886725c9e construction uses the P2 M Ground Theory Heights  Heights Pts Integral Points pts Integral At eq c05886725c9e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPtsIntegralPoints.lean#L59-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPtsIntegralPoints.lean#L59-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPtsIntegralPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G MeasureTheory
open GroundTheory.Heights₂.Heights.PtsIntegralPoints
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_ptsIntegralAt_eq_c05886725c9e [Nonempty K] (P : Ideal (Geo.MRing ι)) (hP : Geo.IsMultiHomogIdeal P)
    (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (hΨ : Geo.IsGoodProj P Ψ) :
    Geo.ptsIntegralAt P Ψ Fin.elim0 g = ∑ᶠ q : projPts P, g (Quot.out q : Geo.mcPts P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsIntegralPoints».«ptsIntegralAt_eq» := P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_ptsIntegralAt_eq_c05886725c9e
