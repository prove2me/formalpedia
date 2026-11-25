-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_generated_pow_505c8b42e2a0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_generated_pow_505c8b42e2a0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:58:50.950566+00:00
-- url     : https://prove2.me/theorems/f4f61bc4-7e69-450d-ab17-c8db99169e4e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System generated pow 505c8b42e2a0: P2 M Ground Theory Heights  Heights Kleiman Sub System generated pow 505c8b42e2a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System generated pow 505c8b42e2a0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System generated pow 505c8b42e2a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L82-L86

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_generated_pow_505c8b42e2a0 {Q : SubSystem k x Ω} (hQ : Q.Generated) (n : ℕ) :
    (Q.pow n).Generated := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«generated_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_generated_pow_505c8b42e2a0
