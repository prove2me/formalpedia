-- Prove2me | Theorems.Thm_SoficGroups_KunActualSoficRootRadius_finiteRootBad_injective_word_evaluation
-- name    : SoficGroups.KunActualSoficRootRadius.finiteRootBad_injective_word_evaluation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/33c5ac47-cb92-46c2-8803-327a8c2d1fe4
-- title:
--   SoficGroups.KunActualSoficRootRadius.finiteRootBad_injective_word_evaluation
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise

theorem SoficGroups.KunActualSoficRootRadius.finiteRootBad_injective_word_evaluation
    {G : Type*} [Group G]
    (M : SoficGroups.PermutationModel G) (F : Finset G)
    {x : Fin M.size} (hx : x ∉ finiteRootBad M F) :
    Set.InjOn (fun g : G => M.action g x) (↑F : Set G) := by sorry
