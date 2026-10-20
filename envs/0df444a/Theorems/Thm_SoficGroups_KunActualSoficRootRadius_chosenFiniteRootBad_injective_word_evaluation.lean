-- Prove2me | Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenFiniteRootBad_injective_word_evaluation
-- name    : SoficGroups.KunActualSoficRootRadius.chosenFiniteRootBad_injective_word_evaluation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/39432e3e-d877-4536-ba89-65bc68d07475
-- title:
--   SoficGroups.KunActualSoficRootRadius.chosenFiniteRootBad_injective_word_evaluation
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

theorem SoficGroups.KunActualSoficRootRadius.chosenFiniteRootBad_injective_word_evaluation
    {G ι : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (F : Finset G) (n : ℕ)
    {x : Fin (A.model n).size}
    (hx : x ∉ chosenFiniteRootBad A s w F n) :
    Set.InjOn (fun g : G => (A.model n).action g x)
      (↑F : Set G) := by sorry
