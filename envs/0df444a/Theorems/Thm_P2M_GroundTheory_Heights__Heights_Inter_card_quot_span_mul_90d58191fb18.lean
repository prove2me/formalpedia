-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_card_quot_span_mul_90d58191fb18
-- name    : P2M_GroundTheory_Heights__Heights_Inter_card_quot_span_mul_90d58191fb18
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:25:11.457833+00:00
-- url     : https://prove2.me/theorems/cd9ebd75-ffaf-4fc7-921e-2f76c0e74019
-- title:
--   P2 M Ground Theory Heights  Heights Inter card quot span mul 90d58191fb18: P2 M Ground Theory Heights  Heights Inter card quot span mul 90d58191fb18
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter card quot span mul 90d58191fb18 construction uses the P2 M Ground Theory Heights  Heights Inter card quot span mul 90d58191fb18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LogCardLocIdealUnitMul.lean#L16-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LogCardLocIdealUnitMul.lean#L16-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_XcNotMemOfIsRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TwoMemFunFieldSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LogCardLocIdealUnitMul
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_card_quot_span_mul_90d58191fb18 {S : Type*} [CommRing S] [IsDomain S] (u v : S) (hu : u ≠ 0) :
    Nat.card (S ⧸ Ideal.span {u * v}) = Nat.card (S ⧸ Ideal.span {u}) * Nat.card (S ⧸ Ideal.span {v}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«card_quot_span_mul» := P2M_GroundTheory_Heights__Heights_Inter_card_quot_span_mul_90d58191fb18
