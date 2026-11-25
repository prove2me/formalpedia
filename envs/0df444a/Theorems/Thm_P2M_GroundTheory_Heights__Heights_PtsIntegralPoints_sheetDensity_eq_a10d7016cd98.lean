-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_sheetDensity_eq_a10d7016cd98
-- name    : P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_sheetDensity_eq_a10d7016cd98
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:02:30.439816+00:00
-- url     : https://prove2.me/theorems/44c66234-ff10-4137-9ca2-bacb9f65d65a
-- title:
--   P2 M Ground Theory Heights  Heights Pts Integral Points sheet Density eq a10d7016cd98: P2 M Ground Theory Heights  Heights Pts Integral Points sheet Density eq a10d7016cd98
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Integral Points sheet Density eq a10d7016cd98 construction uses the P2 M Ground Theory Heights  Heights Pts Integral Points sheet Density eq a10d7016cd98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPtsIntegralPoints.lean#L40-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/PPtsIntegralPoints.lean#L40-L57

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

theorem P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_sheetDensity_eq_a10d7016cd98 (P : Ideal (Geo.MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z)
    (y : Fin 0 → ℂ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ Geo.mcPts P)
    (hΨ : Ψ (Geo.segre z) = Fin.cons 1 y) :
    Geo.sheetDensity P Ψ Fin.elim0 g y (Geo.segre z) = g z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsIntegralPoints».«sheetDensity_eq» := P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_sheetDensity_eq_a10d7016cd98
