-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_eq_pow_ebcff08057ae
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_eq_pow_ebcff08057ae
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:20:55.916269+00:00
-- url     : https://prove2.me/theorems/611c2076-44f5-52d1-bfc1-140646f42513
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sub System pow sub eq pow ebcff08057ae: P2 M Ground Theory Heights  Heights Kleiman Sub System pow sub eq pow ebcff08057ae
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sub System pow sub eq pow ebcff08057ae construction uses the P2 M Ground Theory Heights  Heights Kleiman Sub System pow sub eq pow ebcff08057ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefPlusAmple.lean#L49-L53

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_eq_pow_ebcff08057ae (Q : SubSystem k x Ω) (n : ℕ) (I : Chart x) :
    (Q.pow n).sub I = Q.sub I ^ n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SubSystem».«pow_sub_eq_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_eq_pow_ebcff08057ae
