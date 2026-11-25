-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsPosDens_exists_bound_208a4b055f2a
-- name    : P2M_GroundTheory_Heights__Heights_PtsPosDens_exists_bound_208a4b055f2a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:22:49.966383+00:00
-- url     : https://prove2.me/theorems/d553bb12-42fa-5630-9a4f-f5dd213a8fde
-- title:
--   P2 M Ground Theory Heights  Heights Pts Pos Dens exists bound 208a4b055f2a: P2 M Ground Theory Heights  Heights Pts Pos Dens exists bound 208a4b055f2a
-- statement:
--   The P2 M Ground Theory Heights  Heights Pts Pos Dens exists bound 208a4b055f2a construction uses the P2 M Ground Theory Heights  Heights Pts Pos Dens exists bound 208a4b055f2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsPosDensMeasurable.lean#L35-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PtsPosDensMeasurable.lean#L35-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsPosDensMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.PtsPosDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_PtsPosDens_exists_bound_208a4b055f2a {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    ∃ M : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → |g z| ≤ M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PtsPosDens».«exists_bound» := P2M_GroundTheory_Heights__Heights_PtsPosDens_exists_bound_208a4b055f2a
