-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_ratioField_map_a99e13e3712a
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_ratioField_map_a99e13e3712a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:43.140535+00:00
-- url     : https://prove2.me/theorems/ede32667-c1b2-4abe-a75f-13b1f333ed81
-- title:
--   P2 M Ground Theory Heights  Heights Targets Coord Ratio Deg ratio Field map a99e13e3712a: P2 M Ground Theory Heights  Heights Targets Coord Ratio Deg ratio Field map a99e13e3712a
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Coord Ratio Deg ratio Field map a99e13e3712a construction uses the P2 M Ground Theory Heights  Heights Targets Coord Ratio Deg ratio Field map a99e13e3712a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCoordRatioDeg.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCoordRatioDeg.lean#L16-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_CoordRatioDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCoordRatioDeg
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg

theorem P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_ratioField_map_a99e13e3712a {S M N : Type*} [Field M] [CharZero M] [Field N] [CharZero N] (R : S → S → Prop)
    (z : S → M) (f : M →ₐ[ℚ] N) : (ratioField R z).map f = ratioField R (f ∘ z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CoordRatioDeg».«ratioField_map» := P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_ratioField_map_a99e13e3712a
