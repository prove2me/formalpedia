-- Prove2me | Theorems.Thm_Research_not_eventualShellSixUnorderedBound
-- name    : Research.not_eventualShellSixUnorderedBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:02:49.335805+00:00
-- url     : https://prove2.me/theorems/ad8da1f6-921f-5687-bad4-a84cb0eedf1b
-- title:
--   Research: not eventual Shell Six Unordered Bound
-- statement:
--   No sufficiently-large cutoff can rescue the direct unordered version.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L887-L898
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L887-L898

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.not_eventualShellSixUnorderedBound :
    ¬ EventualShellSixUnorderedBound := by sorry
