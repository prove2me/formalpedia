-- Prove2me | Theorems.Thm_SoficGroups_KunDiagonalGoodRootGraphLoss_permutationGraph_sdiff_goodPermutationGraph_subset
-- name    : SoficGroups.KunDiagonalGoodRootGraphLoss.permutationGraph_sdiff_goodPermutationGraph_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/ebda09f4-5be8-4023-8357-f7b28e457767
-- title:
--   SoficGroups.KunDiagonalGoodRootGraphLoss.permutationGraph_sdiff_goodPermutationGraph_subset
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDiagonalGoodRootGraphLoss
open scoped BigOperators symmDiff

theorem SoficGroups.KunDiagonalGoodRootGraphLoss.permutationGraph_sdiff_goodPermutationGraph_subset {V : Type*}
    [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (B : Finset V) :
    SoficGroups.permutationGraph p \ goodPermutationGraph p B ⊆
      ((SoficGroups.permutationGraph p).filter fun z => z.1 ∈ B) ∪
        ((SoficGroups.permutationGraph p).filter fun z => z.2 ∈ B) := by sorry
