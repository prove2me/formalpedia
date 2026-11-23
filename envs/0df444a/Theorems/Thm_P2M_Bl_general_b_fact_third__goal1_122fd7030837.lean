-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact_third__goal1_122fd7030837
-- name    : P2M_Bl_general_b_fact_third__goal1_122fd7030837
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:31.475282+00:00
-- url     : https://prove2.me/theorems/a9e3c4ba-448f-46d7-9742-fa7937f5273b
-- title:
--   P2 M Bl general b fact third  goal1 122fd7030837: P2 M Bl general b fact third  goal1 122fd7030837
-- statement:
--   The P2 M Bl general b fact third  goal1 122fd7030837 construction uses the P2 M Bl general b fact third  goal1 122fd7030837 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdMore/Key.lean#L15-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdMore/Key.lean#L15-L45

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdMore_Key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third'

theorem P2M_Bl_general_b_fact_third__goal1_122fd7030837 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {n : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) (Fin n → E)),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L)) Top.top.{0} →
    ∀ (w : Fin n → E),
      Exists.{1} fun (m : Nat) ↦ And (LT.lt.{0} 0 m) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} m w)) := by sorry

alias «Bl».«general_b_fact_third'».«goal1» := P2M_Bl_general_b_fact_third__goal1_122fd7030837
