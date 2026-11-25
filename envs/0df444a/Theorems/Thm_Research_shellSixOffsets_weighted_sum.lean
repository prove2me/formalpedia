-- Prove2me | Theorems.Thm_Research_shellSixOffsets_weighted_sum
-- name    : Research.shellSixOffsets_weighted_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:53:13.739829+00:00
-- url     : https://prove2.me/theorems/53e2e546-0763-43d6-9261-4c3530bbb459
-- title:
--   Research: shell Six Offsets weighted sum
-- statement:
--   Exact boundary statistics for the `365 × 365` patch.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L50-L53
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L50-L53

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.shellSixOffsets_weighted_sum :
    ∑ d ∈ shellSixOffsets,
      (365 - d.1.natAbs) * (365 - d.2.natAbs) = 16786618 := by sorry
