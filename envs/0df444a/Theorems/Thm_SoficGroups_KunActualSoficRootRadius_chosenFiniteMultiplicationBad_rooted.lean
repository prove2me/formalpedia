-- Prove2me | Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenFiniteMultiplicationBad_rooted
-- name    : SoficGroups.KunActualSoficRootRadius.chosenFiniteMultiplicationBad_rooted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/a061906f-e2ab-41fd-a3fb-cd75c302e668
-- title:
--   SoficGroups.KunActualSoficRootRadius.chosenFiniteMultiplicationBad_rooted
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

theorem SoficGroups.KunActualSoficRootRadius.chosenFiniteMultiplicationBad_rooted
    {G ι : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (F : Finset G) (n : ℕ)
    {g h : G} (hg : g ∈ F) (hh : h ∈ F)
    {x : Fin (A.model n).size}
    (hx : x ∉ chosenFiniteMultiplicationBad A s w F n) :
    chosenWordEvaluation A s w n (g * h) x =
      (chosenWordEvaluation A s w n g *
        chosenWordEvaluation A s w n h) x := by sorry
