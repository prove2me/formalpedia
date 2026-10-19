-- Prove2me | Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_card_goodPermutationGraph_add_graph_loss
-- name    : SoficGroups.KunDiagonalGoodRootGraphLoss.card_goodPermutationGraph_add_graph_loss
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/aa21d2a4-7f1d-4573-b5de-c85692fa0881
-- title:
--   SoficGroups.KunDiagonalGoodRootGraphLoss.card_goodPermutationGraph_add_graph_loss
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDiagonalGoodRootGraphLoss
open scoped BigOperators symmDiff

theorem SoficGroups.KunDiagonalGoodRootGraphLoss.card_goodPermutationGraph_add_graph_loss {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    (SoficGroups.permutationGraph p \ goodPermutationGraph p B).card +
        (goodPermutationGraph p B).card = Fintype.card V := by sorry
