-- Prove2me | Theorems.Thm_P2M_RH_P2M_Bl_general_b_fact________goal1_21b1a474250b_b320b26946e406da
-- name    : P2M_RH_P2M_Bl_general_b_fact________goal1_21b1a474250b_b320b26946e406da
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:13.446662+00:00
-- url     : https://prove2.me/theorems/f629137e-c689-485b-931f-1e8bc68d94fb
-- title:
--   P2 M RH P2 M Bl general b fact        goal1 21b1a474250b b320b26946e406da: P2 M RH P2 M Bl general b fact        goal1 21b1a474250b b320b26946e406da
-- statement:
--   The P2 M RH P2 M Bl general b fact        goal1 21b1a474250b b320b26946e406da construction uses the P2 M RH P2 M Bl general b fact        goal1 21b1a474250b b320b26946e406da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLast/Imports.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLast/Imports.lean#L7-L20

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLast_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.general_b_fact'''''''

theorem P2M_RH_P2M_Bl_general_b_fact________goal1_21b1a474250b_b320b26946e406da :
  ∀ {O : Type u_1} [inst : CommRing.{u_1} O] [inst_1 : IsDomain.{u_1} O] [inst_2 : IsDiscreteValuationRing.{u_1} O]
  {ι : Type u_2} (s : Finset.{u_2} ι) (a : ι → O),
  Eq.{1}
    (DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O)
      (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ a i))
    (Finset.sum.{u_2, 0} s fun (i : ι) ↦
      DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O) (a i)) := by sorry

alias «Bl».«general_b_fact'''''''».«goal1» := P2M_RH_P2M_Bl_general_b_fact________goal1_21b1a474250b_b320b26946e406da
