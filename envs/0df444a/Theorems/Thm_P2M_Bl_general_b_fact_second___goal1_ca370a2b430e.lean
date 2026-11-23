-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact_second___goal1_ca370a2b430e
-- name    : P2M_Bl_general_b_fact_second___goal1_ca370a2b430e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:35.128457+00:00
-- url     : https://prove2.me/theorems/fce07b71-92f4-42f2-b365-86fb8cc334ed
-- title:
--   P2 M Bl general b fact second   goal1 ca370a2b430e: P2 M Bl general b fact second   goal1 ca370a2b430e
-- statement:
--   The P2 M Bl general b fact second   goal1 ca370a2b430e construction uses the P2 M Bl general b fact second   goal1 ca370a2b430e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondFurther/Imports.lean#L5-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondFurther/Imports.lean#L5-L34

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second''

theorem P2M_Bl_general_b_fact_second___goal1_ca370a2b430e :
  ∀ {O K X : Type} [inst : CommRing.{0} O] [IsDomain.{0} O] [inst_2 : Field.{0} K] [inst_3 : Algebra.{0, 0} O K]
  [IsFractionRing.{0, 0} O K] [inst_5 : AddCommGroup.{0} X] [inst_6 : Module.{0, 0} K X] [inst_7 : Module.{0, 0} O X]
  [IsScalarTower.{0, 0, 0} O K X] (B : Submodule.{0, 0} O X),
  Eq.{1} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} B)) Top.top.{0} →
    ∀ (x : X), Exists.{1} fun (d : O) ↦ And (Ne.{1} d 0) (Membership.mem.{0, 0} B (HSMul.hSMul.{0, 0, 0} d x)) := by sorry

alias «Bl».«general_b_fact_second''».«goal1» := P2M_Bl_general_b_fact_second___goal1_ca370a2b430e
