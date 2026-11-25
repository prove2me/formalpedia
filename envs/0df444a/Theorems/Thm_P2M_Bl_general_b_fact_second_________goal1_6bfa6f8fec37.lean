-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact_second_________goal1_6bfa6f8fec37
-- name    : P2M_Bl_general_b_fact_second_________goal1_6bfa6f8fec37
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:32.942519+00:00
-- url     : https://prove2.me/theorems/a53efcec-725e-40a8-be1d-132d3319af41
-- title:
--   P2 M Bl general b fact second         goal1 6bfa6f8fec37: P2 M Bl general b fact second         goal1 6bfa6f8fec37
-- statement:
--   The P2 M Bl general b fact second         goal1 6bfa6f8fec37 construction uses the P2 M Bl general b fact second         goal1 6bfa6f8fec37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondBisAlt/Imports.lean#L5-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondBisAlt/Imports.lean#L5-L40

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondBisAlt_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second''''''''

theorem P2M_Bl_general_b_fact_second_________goal1_6bfa6f8fec37 :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} K V] [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  (M : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V) {x : V},
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} M)) x →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} d 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} d x)) := by sorry

alias «Bl».«general_b_fact_second''''''''».«goal1» := P2M_Bl_general_b_fact_second_________goal1_6bfa6f8fec37
