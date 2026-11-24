-- Prove2me | Theorems.Thm_P2M_Kirkman_SteinerOp_op_op_right__bbbfe2541011
-- name    : P2M_Kirkman_SteinerOp_op_op_right__bbbfe2541011
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:08.413108+00:00
-- url     : https://prove2.me/theorems/a973e8f5-bc76-471f-9736-0d3b83288c89
-- title:
--   P2 M Kirkman Steiner Op op op right  bbbfe2541011: P2 M Kirkman Steiner Op op op right  bbbfe2541011
-- statement:
--   The P2 M Kirkman Steiner Op op op right  bbbfe2541011 construction uses the P2 M Kirkman Steiner Op op op right  bbbfe2541011 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L69-L69
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/KirkmanLib/SteinerOp.lean#L69-L69

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman
variable {P : Type*}
open Kirkman.SteinerOp
variable (S : SteinerOp P)
variable [DecidableEq P]
omit [DecidableEq P]

theorem P2M_Kirkman_SteinerOp_op_op_right__bbbfe2541011 (x y : P) : S.op (S.op x y) y = x := by sorry

alias «Kirkman».«SteinerOp».«op_op_right'» := P2M_Kirkman_SteinerOp_op_op_right__bbbfe2541011
