-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormRank_holds_eq_zero_of_eventually_eval_602689fad780
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pointFormRank_holds_eq_zero_of_eventually_eval_602689fad780
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:37.564861+00:00
-- url     : https://prove2.me/theorems/787393b6-c1cc-46ca-b299-25a088f1c2f3
-- title:
--   P2 M Ground Theory Heights  Heights Inter point Form Rank holds eq zero of eventually eval 602689fad780: P2 M Ground Theory Heights  Heights Inter point Form Rank holds eq zero of eventually eval 6026
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter point Form Rank holds eq zero of eventually eval 602689fad780 construction uses the P2 M Ground Theory Heights  Heights Inter point Form Rank holds eq zero of eventually eval 602689fad780 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/EqZeroOfEventuallyEval.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/EqZeroOfEventuallyEval.lean#L44-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMapAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRatioAlgDep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_EqZeroOfEventuallyEval
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Inter_pointFormRank_holds_eq_zero_of_eventually_eval_602689fad780 {d : ℕ} (f : MvPolynomial (Fin d) ℂ) (a : Fin d → ℂ)
    (h : ∀ᶠ z in 𝓝 a, eval z f = 0) : f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pointFormRank_holds».«eq_zero_of_eventually_eval» := P2M_GroundTheory_Heights__Heights_Inter_pointFormRank_holds_eq_zero_of_eventually_eval_602689fad780
