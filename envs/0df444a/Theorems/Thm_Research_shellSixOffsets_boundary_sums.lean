-- Prove2me | Theorems.Thm_Research_shellSixOffsets_boundary_sums
-- name    : Research.shellSixOffsets_boundary_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:07:23.271839+00:00
-- url     : https://prove2.me/theorems/514465ff-2c9d-5416-9571-fb3464fb1dc7
-- title:
--   Research: shell Six Offsets boundary sums
-- statement:
--   Two auxiliary exact boundary statistics, useful for an independent audit
--   of the weighted count.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L57-L60
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L57-L60

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.shellSixOffsets_boundary_sums :
    (∑ d ∈ shellSixOffsets, (d.1.natAbs + d.2.natAbs)) = 732 ∧
    (∑ d ∈ shellSixOffsets, d.1.natAbs * d.2.natAbs) = 998 := by sorry
