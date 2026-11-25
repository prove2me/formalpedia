-- Prove2me | Theorems.Thm_Research_shellSixIncidence_card
-- name    : Research.shellSixIncidence_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:48:02.990793+00:00
-- url     : https://prove2.me/theorems/8ed02077-b0f1-5a6f-afdf-a14e3bdec9ef
-- title:
--   Research: shell Six Incidence card
-- statement:
--   There are exactly 16,786,618 certified directed incidences; the proof
--   reduces the dependent cardinality to the 169-cell offset census rather than
--   enumerating the inhabitants.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L389-L401
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L389-L401

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.shellSixIncidence_card :
    Fintype.card ShellSixIncidence = 16786618 := by sorry
