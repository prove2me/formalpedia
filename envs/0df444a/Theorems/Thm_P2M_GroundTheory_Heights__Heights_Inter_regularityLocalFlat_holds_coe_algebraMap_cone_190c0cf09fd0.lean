-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coe_algebraMap_cone_190c0cf09fd0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coe_algebraMap_cone_190c0cf09fd0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:07.69205+00:00
-- url     : https://prove2.me/theorems/355a6a95-b1f6-4b92-9baf-f590b2b6397c
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds coe algebra Map cone 190c0cf09fd0: P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds coe algebra Map cone 190c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds coe algebra Map cone 190c0cf09fd0 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Local Flat holds coe algebra Map cone 190c0cf09fd0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean#L23-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coe_algebraMap_cone_190c0cf09fd0 (hPW : P ≤ W) (a : MRing ι ⧸ P) :
    ((algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) a : coneLocRing P W hPW) : FractionRing (MRing ι ⧸ P)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityLocalFlat_holds».«coe_algebraMap_cone» := P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coe_algebraMap_cone_190c0cf09fd0
