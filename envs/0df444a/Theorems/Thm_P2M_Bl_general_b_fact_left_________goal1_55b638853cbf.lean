-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact_left_________goal1_55b638853cbf
-- name    : P2M_Bl_general_b_fact_left_________goal1_55b638853cbf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:29.514251+00:00
-- url     : https://prove2.me/theorems/761981b6-f97a-4cca-aa1e-96e7b1d9b424
-- title:
--   P2 M Bl general b fact left         goal1 55b638853cbf: P2 M Bl general b fact left         goal1 55b638853cbf
-- statement:
--   The P2 M Bl general b fact left         goal1 55b638853cbf construction uses the P2 M Bl general b fact left         goal1 55b638853cbf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftBisAlt/Imports.lean#L5-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftBisAlt/Imports.lean#L5-L38

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftBisAlt_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_left''''''''

theorem P2M_Bl_general_b_fact_left_________goal1_55b638853cbf :
  ∀ {K V : Type} [inst : Field.{0} K] [NumberField.{0} K] [inst_2 : AddCommGroup.{0} V] [inst_3 : Module.{0, 0} K V]
  [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V) (v : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} d 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} d v)) := by sorry

alias «Bl».«general_b_fact_left''''''''».«goal1» := P2M_Bl_general_b_fact_left_________goal1_55b638853cbf
