-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_mul_59a410201a68
-- name    : P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_mul_59a410201a68
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:57.833615+00:00
-- url     : https://prove2.me/theorems/06cbd602-c4f2-4eaf-989d-c506ad6840a6
-- title:
--   P2 M Ground Theory Heights  Heights Inter log card loc Ideal mul 59a410201a68: P2 M Ground Theory Heights  Heights Inter log card loc Ideal mul 59a410201a68
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter log card loc Ideal mul 59a410201a68 construction uses the P2 M Ground Theory Heights  Heights Inter log card loc Ideal mul 59a410201a68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LogCardLocIdealUnitMul.lean#L44-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LogCardLocIdealUnitMul.lean#L44-L54

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

theorem P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_mul_59a410201a68 {P W : Ideal (MRing ι)} [P.IsPrime] {y₁ y₂ : FractionRing (MRing ι ⧸ P)}
    (h₁ : y₁ ∈ locRing P W) (h₂ : y₂ ∈ locRing P W) (hne : y₁ ≠ 0)
    (hf₁ : Finite (locRing P W ⧸ locIdeal P W y₁)) (hf₂ : Finite (locRing P W ⧸ locIdeal P W y₂)) :
    Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y₁ * y₂))) =
      Real.log (Nat.card (locRing P W ⧸ locIdeal P W y₁)) + Real.log (Nat.card (locRing P W ⧸ locIdeal P W y₂)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«log_card_locIdeal_mul» := P2M_GroundTheory_Heights__Heights_Inter_log_card_locIdeal_mul_59a410201a68
