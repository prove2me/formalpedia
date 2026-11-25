-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_of_eq_zero_44fe3d743ff6
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_of_eq_zero_44fe3d743ff6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:01:15.965472+00:00
-- url     : https://prove2.me/theorems/832140a0-069d-463c-bd30-e19102989e87
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman is Very Ample of eq zero 44fe3d743ff6: P2 M Ground Theory Heights  Heights Kleiman is Very Ample of eq zero 44fe3d743ff6
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman is Very Ample of eq zero 44fe3d743ff6 construction uses the P2 M Ground Theory Heights  Heights Kleiman is Very Ample of eq zero 44fe3d743ff6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L159-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L159-L164

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_of_eq_zero_44fe3d743ff6 (hx : x = 0) (F : SubSystem k x Ω) : IsVeryAmple F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«isVeryAmple_of_eq_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_of_eq_zero_44fe3d743ff6
