-- Prove2me | Theorems.Thm_Research_obliqueBlocks_oneSeparated
-- name    : Research.obliqueBlocks_oneSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:52:29.377396+00:00
-- url     : https://prove2.me/theorems/347de7de-3f24-46c1-9b57-f85a1d9e6de6
-- title:
--   Research: oblique Blocks one Separated
-- statement:
--   Every replicated configuration remains one-separated.
--
--   Source: https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L659-L692
-- source:
--   https://github.com/AItoBit/erdos-662-proof/blob/91f70364bf88c9ae8181aa82a703a7ba2d369901/Research/GlobalShellSix.lean#L659-L692

module
public import Definitions.Def_Research_TriangularShells
public import Definitions.Def_Research_GlobalShellSix
set_option autoImplicit true
@[expose] public section
public section
open Research
set_option maxRecDepth 100000
attribute [local instance] Research.prodLexLinearOrder

theorem Research.obliqueBlocks_oneSeparated (m : ℕ) :
    ∀ q s : Fin m × (Fin 365 × Fin 365), q ≠ s →
      1 ≤ sqDist (obliqueBlocks m q) (obliqueBlocks m s) := by sorry
