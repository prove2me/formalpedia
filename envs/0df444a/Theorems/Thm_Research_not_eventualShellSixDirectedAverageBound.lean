-- Prove2me | Theorems.Thm_Research_not_eventualShellSixDirectedAverageBound
-- name    : Research.not_eventualShellSixDirectedAverageBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:52:57.366619+00:00
-- url     : https://prove2.me/theorems/d0594df7-c8d6-4a5e-9090-f579d2738a42
-- title:
--   Research: not eventual Shell Six Directed Average Bound
-- statement:
--   No sufficiently-large cutoff can rescue the directed global-average
--   reading at the genuine triangular shell radius six.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L873-L884
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L873-L884

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.not_eventualShellSixDirectedAverageBound :
    ¬ EventualShellSixDirectedAverageBound := by sorry
