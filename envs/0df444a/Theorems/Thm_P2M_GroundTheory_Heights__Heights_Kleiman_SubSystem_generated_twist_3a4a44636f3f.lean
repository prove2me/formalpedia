-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_generated_twist_3a4a44636f3f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_generated_twist_3a4a44636f3f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:58:45.272212+00:00
-- url     : https://prove2.me/theorems/2163016d-8072-463d-9a43-3fc5d733c9a4
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System generated twist 3a4a44636f3f: P2 M Ground Theory Heights  Heights Kleiman Sub System generated twist 3a4a44636f3f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System generated twist 3a4a44636f3f construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System generated twist 3a4a44636f3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L61-L71

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_generated_twist_3a4a44636f3f {F Q : SubSystem k x Ω} (hF : F.Generated) (hQ : Q.Generated) :
    (F.twist Q).Generated := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«generated_twist» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_generated_twist_3a4a44636f3f
