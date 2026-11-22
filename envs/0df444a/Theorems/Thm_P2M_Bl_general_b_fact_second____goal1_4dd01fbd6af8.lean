-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact_second____goal1_4dd01fbd6af8
-- name    : P2M_Bl_general_b_fact_second____goal1_4dd01fbd6af8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:21:49.011446+00:00
-- url     : https://prove2.me/theorems/11d29c16-784c-4b7c-921a-7fbb374e5a9c
-- title:
--   P2 M Bl general b fact second    goal1 4dd01fbd6af8: P2 M Bl general b fact second    goal1 4dd01fbd6af8
-- statement:
--   The P2 M Bl general b fact second    goal1 4dd01fbd6af8 construction uses the P2 M Bl general b fact second    goal1 4dd01fbd6af8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondExtra/Key.lean#L41-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactSecondExtra/Key.lean#L41-L59

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact_second'''

theorem P2M_Bl_general_b_fact_second____goal1_4dd01fbd6af8 :
  ∀ {O : Type u_1} {Y : Type u_2} [inst : CommRing.{u_1} O] [inst_1 : AddCommGroup.{u_2} Y]
  [inst_2 : Module.{u_1, u_2} O Y] (R S D E : Submodule.{u_1, u_2} O Y),
  (∀ (y : Y),
      Iff (Membership.mem.{u_2, u_2} D y) (And (Membership.mem.{u_2, u_2} R y) (Membership.mem.{u_2, u_2} S y))) →
    LE.le.{u_2} E D →
      Eq.{1}
        (Module.length.{u_1, u_2} O
          (HasQuotient.Quotient.{u_2, u_2} (Subtype.{u_2 + 1} fun (x : Y) ↦ Membership.mem.{u_2, u_2} R x)
            (Submodule.comap.{u_1, u_1, u_2, u_2} (Submodule.subtype.{u_1, u_2} R) E)))
        (HAdd.hAdd.{0, 0, 0}
          (Module.length.{u_1, u_2} O
            (HasQuotient.Quotient.{u_2, u_2} (Subtype.{u_2 + 1} fun (x : Y) ↦ Membership.mem.{u_2, u_2} R x)
              (Submodule.comap.{u_1, u_1, u_2, u_2} (Submodule.subtype.{u_1, u_2} R) S)))
          (Module.length.{u_1, u_2} O
            (HasQuotient.Quotient.{u_2, u_2} (Subtype.{u_2 + 1} fun (x : Y) ↦ Membership.mem.{u_2, u_2} D x)
              (Submodule.comap.{u_1, u_1, u_2, u_2} (Submodule.subtype.{u_1, u_2} D) E)))) := by sorry

alias «Bl».«general_b_fact_second'''».«goal1» := P2M_Bl_general_b_fact_second____goal1_4dd01fbd6af8
