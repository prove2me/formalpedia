-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact_second__goal1_bb5a16c38fea
-- name    : P2M_Bl_general_b_fact_second__goal1_bb5a16c38fea
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:31.243716+00:00
-- url     : https://prove2.me/theorems/5920b911-cf8d-484c-bdf1-474320dc5dbe
-- title:
--   P2 M Bl general b fact second  goal1 bb5a16c38fea: P2 M Bl general b fact second  goal1 bb5a16c38fea
-- statement:
--   The P2 M Bl general b fact second  goal1 bb5a16c38fea construction uses the P2 M Bl general b fact second  goal1 bb5a16c38fea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondMore/Imports.lean#L5-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondMore/Imports.lean#L5-L36

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second'

theorem P2M_Bl_general_b_fact_second__goal1_bb5a16c38fea :
  ∀ {E U : Type} [inst : Field.{0} E] [NumberField.{0} E] [inst_2 : AddCommGroup.{0} U] [inst_3 : Module.{0, 0} E U]
  [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} E) U]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E U]
  (N : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) U),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} N)) Top.top.{0} →
    ∀ (x : U),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} N (HSMul.hSMul.{0, 0, 0} d x)) := by sorry

alias «Bl».«general_b_fact_second'».«goal1» := P2M_Bl_general_b_fact_second__goal1_bb5a16c38fea
