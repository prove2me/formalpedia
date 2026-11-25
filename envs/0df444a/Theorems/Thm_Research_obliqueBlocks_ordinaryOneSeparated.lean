-- Prove2me | Theorems.Thm_Research_obliqueBlocks_ordinaryOneSeparated
-- name    : Research.obliqueBlocks_ordinaryOneSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:47:51.980843+00:00
-- url     : https://prove2.me/theorems/d0b25d7e-b992-58de-9383-9b9f5606d140
-- title:
--   Research: oblique Blocks ordinary One Separated
-- statement:
--   The translated blocks are one-separated in ordinary-distance notation.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L833-L837
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L833-L837

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.obliqueBlocks_ordinaryOneSeparated (m : ℕ) :
    OrdinaryOneSeparatedOn (obliqueBlocks m) := by sorry
