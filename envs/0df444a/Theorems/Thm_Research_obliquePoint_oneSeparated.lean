-- Prove2me | Theorems.Thm_Research_obliquePoint_oneSeparated
-- name    : Research.obliquePoint_oneSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:57:22.024745+00:00
-- url     : https://prove2.me/theorems/cbb80f81-727d-5888-9d01-d182545438b1
-- title:
--   Research: oblique Point one Separated
-- statement:
--   Every patch is one-separated.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L218-L242
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L218-L242

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.obliquePoint_oneSeparated :
    ∀ q s : Fin 365 × Fin 365, q ≠ s →
      1 ≤ sqDist (obliquePoint q) (obliquePoint s) := by sorry
