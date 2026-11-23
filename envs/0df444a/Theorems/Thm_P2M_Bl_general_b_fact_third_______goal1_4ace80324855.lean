-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact_third_______goal1_4ace80324855
-- name    : P2M_Bl_general_b_fact_third_______goal1_4ace80324855
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:43.557321+00:00
-- url     : https://prove2.me/theorems/f3ebfba4-5849-4bea-9b4c-f04cb5f65632
-- title:
--   P2 M Bl general b fact third       goal1 4ace80324855: P2 M Bl general b fact third       goal1 4ace80324855
-- statement:
--   The P2 M Bl general b fact third       goal1 4ace80324855 construction uses the P2 M Bl general b fact third       goal1 4ace80324855 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdTail/Imports.lean#L5-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdTail/Imports.lean#L5-L36

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdTail_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third''''''

theorem P2M_Bl_general_b_fact_third_______goal1_4ace80324855 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} E V] [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} E) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E V]
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) V),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} Λ)) Top.top.{0} →
    ∀ (x : V),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} d x)) := by sorry

alias «Bl».«general_b_fact_third''''''».«goal1» := P2M_Bl_general_b_fact_third_______goal1_4ace80324855
