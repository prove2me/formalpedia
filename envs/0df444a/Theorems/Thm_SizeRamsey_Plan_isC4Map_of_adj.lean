-- Prove2me | Theorems.Thm_SizeRamsey_Plan_isC4Map_of_adj
-- name    : SizeRamsey.Plan.isC4Map_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:21:31.018021+00:00
-- url     : https://prove2.me/theorems/35f29b3d-f886-5718-9d54-9c81cc45c506
-- title:
--   Plan: is C4 Map of adj
-- statement:
--   A square presented by its four consecutive vertices.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L69-L75
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean#L69-L75

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan

theorem SizeRamsey.Plan.isC4Map_of_adj {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : IsC4Map G ![a, b, c, d] := by sorry
