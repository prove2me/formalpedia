-- Prove2me | Theorems.Thm_Research_shellSixBlockIncidence_card
-- name    : Research.shellSixBlockIncidence_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:02:41.779802+00:00
-- url     : https://prove2.me/theorems/50ec8374-6422-42ae-aa04-5afb8100ace3
-- title:
--   Research: shell Six Block Incidence card
-- statement:
--   Exact cardinality of the block-incidence type.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L751-L753
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L751-L753

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.shellSixBlockIncidence_card (m : ℕ) :
    Fintype.card (ShellSixBlockIncidence m) = m * 16786618 := by sorry
