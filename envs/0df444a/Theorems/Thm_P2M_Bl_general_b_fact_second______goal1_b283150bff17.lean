-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact_second______goal1_b283150bff17
-- name    : P2M_Bl_general_b_fact_second______goal1_b283150bff17
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T16:49:14.515787+00:00
-- url     : https://prove2.me/theorems/15df5b03-b7e9-4640-bede-632c844f7ae5
-- title:
--   P2 M Bl general b fact second      goal1 b283150bff17: P2 M Bl general b fact second      goal1 b283150bff17
-- statement:
--   The P2 M Bl general b fact second      goal1 b283150bff17 construction uses the P2 M Bl general b fact second      goal1 b283150bff17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondSide/Imports.lean#L5-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondSide/Imports.lean#L5-L41

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondSide_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second'''''

theorem P2M_Bl_general_b_fact_second______goal1_b283150bff17 :
  ∀ {K V : Type} [inst : Field.{0} K] [NumberField.{0} K] [StarRing.{0} K] [inst_3 : AddCommGroup.{0} V]
  [inst_4 : Module.{0, 0} K V] [inst_5 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [inst_6 : IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  (M : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V),
  Submodule.IsLattice.{0, 0, 0} K M →
    ∀ (x : V), Exists.{1} fun (n : Int) ↦ And (Ne.{1} n 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} n x)) := by sorry

alias «Bl».«general_b_fact_second'''''».«goal1» := P2M_Bl_general_b_fact_second______goal1_b283150bff17
