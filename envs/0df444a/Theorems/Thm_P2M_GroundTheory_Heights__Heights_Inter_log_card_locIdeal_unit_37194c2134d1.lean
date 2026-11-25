-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_unit_37194c2134d1
-- name    : P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_unit_37194c2134d1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:55.821846+00:00
-- url     : https://prove2.me/theorems/b2fbebb0-c56a-58e7-8200-b82dbe9108cf
-- title:
--   P2 M Ground Theory Heights  Heights Inter log card loc Ideal unit 37194c2134d1: P2 M Ground Theory Heights  Heights Inter log card loc Ideal unit 37194c2134d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter log card loc Ideal unit 37194c2134d1 construction uses the P2 M Ground Theory Heights  Heights Inter log card loc Ideal unit 37194c2134d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LogCardLocIdealUnitMul.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LogCardLocIdealUnitMul.lean#L56-L63

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_unit_37194c2134d1 {P W : Ideal (MRing ι)} [P.IsPrime] {y z : FractionRing (MRing ι ⧸ P)}
    (hy : y ∈ locRing P W) (hz : z ∈ locRing P W) (h : y * z = 1) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W y)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«log_card_locIdeal_unit» := P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_unit_37194c2134d1
