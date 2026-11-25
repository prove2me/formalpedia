-- Prove2me | Theorems.Thm_Research_not_literalClaimAtOne
-- name    : Research.not_literalClaimAtOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:38:23.382626+00:00
-- url     : https://prove2.me/theorems/a8755f9c-a343-4d4e-9c96-a5d491100acd
-- title:
--   Research: not literal Claim At One
-- statement:
--   The direct reading of the printed conjecture is false.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/Basic.lean#L45-L99
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/Basic.lean#L45-L99

module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Prod.Lex
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_Research_Basic
set_option autoImplicit true
@[expose] public section
public section
open Research

theorem Research.not_literalClaimAtOne : ¬ LiteralClaimAtOne := by sorry
