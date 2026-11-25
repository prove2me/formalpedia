-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_unit_mul_750ad0c2d9bf
-- name    : P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_unit_mul_750ad0c2d9bf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:01.084391+00:00
-- url     : https://prove2.me/theorems/b1f534b2-18d9-407e-bb15-a7bf085a6ae6
-- title:
--   P2 M Ground Theory Heights  Heights Inter log card loc Ideal unit mul 750ad0c2d9bf: P2 M Ground Theory Heights  Heights Inter log card loc Ideal unit mul 750ad0c2d9bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter log card loc Ideal unit mul 750ad0c2d9bf construction uses the P2 M Ground Theory Heights  Heights Inter log card loc Ideal unit mul 750ad0c2d9bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LogCardLocIdealUnitMul.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LogCardLocIdealUnitMul.lean#L65-L71

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

theorem P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_unit_mul_750ad0c2d9bf {P W : Ideal (MRing ι)} [P.IsPrime] {y z c : FractionRing (MRing ι ⧸ P)}
    (hy : y ∈ locRing P W) (hz : z ∈ locRing P W) (h : y * z = 1) (hc : c ∈ locRing P W) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y * c))) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W c)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«log_card_locIdeal_unit_mul» := P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_unit_mul_750ad0c2d9bf
