-- Prove2me | Theorems.Thm_Research_shellSixOffsets_card
-- name    : Research.shellSixOffsets_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:07:20.754589+00:00
-- url     : https://prove2.me/theorems/840c09ee-2421-5801-920e-6ff1d9a29439
-- title:
--   Research: shell Six Offsets card
-- statement:
--   Exact kernel census of the oblique offsets.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L46-L47
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L46-L47

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.shellSixOffsets_card : shellSixOffsets.card = 128 := by sorry
