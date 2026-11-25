-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_eq_mul_d7e23ae652ec
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_eq_mul_d7e23ae652ec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:21:03.099388+00:00
-- url     : https://prove2.me/theorems/b96daf91-7a0e-5242-979f-2390104840a6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System twist sub eq mul d7e23ae652ec: P2 M Ground Theory Heights  Heights Kleiman Sub System twist sub eq mul d7e23ae652ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System twist sub eq mul d7e23ae652ec construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System twist sub eq mul d7e23ae652ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L20-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L20-L30

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_eq_mul_d7e23ae652ec (F Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = F.sub I * Q.sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«twist_sub_eq_mul» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_eq_mul_d7e23ae652ec
