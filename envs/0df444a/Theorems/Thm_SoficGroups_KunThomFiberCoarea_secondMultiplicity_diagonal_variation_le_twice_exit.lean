-- Prove2me | Theorems.Thm_SoficGroups_KunThomFiberCoarea_secondMultiplicity_diagonal_variation_le_twice_exit
-- name    : SoficGroups.KunThomFiberCoarea.secondMultiplicity_diagonal_variation_le_twice_exit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:23.501339+00:00
-- url     : https://prove2.me/theorems/4e9237b3-0546-4e81-a035-55c38e502d26
-- title:
--   SoficGroups.KunThomFiberCoarea.secondMultiplicity_diagonal_variation_le_twice_exit
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea

theorem SoficGroups.KunThomFiberCoarea.secondMultiplicity_diagonal_variation_le_twice_exit
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) :
    (∑ x : V, Nat.dist (secondMultiplicity U (p x))
      (secondMultiplicity U x)) ≤ 2 * diagonalExit p U := by sorry
