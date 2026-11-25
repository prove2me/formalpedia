-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_ratioField_congr_41a5f9c84a95
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_ratioField_congr_41a5f9c84a95
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:33.275649+00:00
-- url     : https://prove2.me/theorems/11eee762-c004-4998-bb2b-c71ce04c8f49
-- title:
--   P2 M Ground Theory Heights  Heights Targets Coord Ratio Deg ratio Field congr 41a5f9c84a95: P2 M Ground Theory Heights  Heights Targets Coord Ratio Deg ratio Field congr 41a5f9c84a95
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Coord Ratio Deg ratio Field congr 41a5f9c84a95 construction uses the P2 M Ground Theory Heights  Heights Targets Coord Ratio Deg ratio Field congr 41a5f9c84a95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCoordRatioDeg.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCoordRatioDeg.lean#L27-L36

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

theorem P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_ratioField_congr_41a5f9c84a95 {S M : Type*} [Field M] [CharZero M] {R : S → S → Prop} {z w : S → M}
    (h : ∀ p q, R p q → z p / z q = w p / w q) : ratioField R z = ratioField R w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CoordRatioDeg».«ratioField_congr» := P2M_GroundTheory_Heights__Heights_Targets_CoordRatioDeg_ratioField_congr_41a5f9c84a95
