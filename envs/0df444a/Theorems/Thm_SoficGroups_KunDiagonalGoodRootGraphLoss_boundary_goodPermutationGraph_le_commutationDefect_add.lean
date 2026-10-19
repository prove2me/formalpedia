-- Prove2me | Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_boundary_goodPermutationGraph_le_commutationDefect_add
-- name    : SoficGroups.KunDiagonalGoodRootGraphLoss.boundary_goodPermutationGraph_le_commutationDefect_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/110fb111-f5b9-4349-adcb-3db6879935cb
-- title:
--   SoficGroups.KunDiagonalGoodRootGraphLoss.boundary_goodPermutationGraph_le_commutationDefect_add
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDiagonalGoodRootGraphLoss
open scoped BigOperators symmDiff

theorem SoficGroups.KunDiagonalGoodRootGraphLoss.boundary_goodPermutationGraph_le_commutationDefect_add {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (p : Equiv.Perm V) (B : Finset V) :
    SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) (goodPermutationGraph p B) ≤
      SoficGroups.permutationCommutationDefect σ p +
        2 * Fintype.card ι * B.card := by sorry
