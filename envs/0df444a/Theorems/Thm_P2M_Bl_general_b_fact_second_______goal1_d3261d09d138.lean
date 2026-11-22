-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact_second_______goal1_d3261d09d138
-- name    : P2M_Bl_general_b_fact_second_______goal1_d3261d09d138
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:09.8498+00:00
-- url     : https://prove2.me/theorems/271d7b5c-2c7b-47c3-ae73-4c4eed83fa27
-- title:
--   P2 M Bl general b fact second       goal1 d3261d09d138: P2 M Bl general b fact second       goal1 d3261d09d138
-- statement:
--   The P2 M Bl general b fact second       goal1 d3261d09d138 construction uses the P2 M Bl general b fact second       goal1 d3261d09d138 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondTail/Imports.lean#L7-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondTail/Imports.lean#L7-L40

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondTail_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact_second''''''

theorem P2M_Bl_general_b_fact_second_______goal1_d3261d09d138 :
  ∀ {K : Type u_1} [inst : Field.{u_1} K] [NumberField.{u_1} K] {V : Type u_2} [inst_2 : AddCommGroup.{u_2} V]
  [inst_3 : Module.{u_1, u_2} K V] [inst_4 : Module.{u_1, u_2} (NumberField.RingOfIntegers.{u_1} K) V]
  [IsScalarTower.{u_1, u_1, u_2} (NumberField.RingOfIntegers.{u_1} K) K V]
  (A : Submodule.{u_1, u_2} (NumberField.RingOfIntegers.{u_1} K) V) (x : V),
  Membership.mem.{u_2, u_2} (Submodule.span.{u_1, u_2} K (SetLike.coe.{u_2, u_2} A)) x →
    Exists.{u_1 + 1} fun (d : NumberField.RingOfIntegers.{u_1} K) ↦
      And (Ne.{u_1 + 1} d 0) (Membership.mem.{u_2, u_2} A (HSMul.hSMul.{u_1, u_2, u_2} d x)) := by sorry

alias «Bl».«general_b_fact_second''''''».«goal1» := P2M_Bl_general_b_fact_second_______goal1_d3261d09d138
