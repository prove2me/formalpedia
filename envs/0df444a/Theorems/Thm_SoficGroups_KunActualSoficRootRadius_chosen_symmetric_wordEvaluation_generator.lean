-- Prove2me | Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosen_symmetric_wordEvaluation_generator
-- name    : SoficGroups.KunActualSoficRootRadius.chosen_symmetric_wordEvaluation_generator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/af2db99d-29b0-4692-a082-4a153ed3a285
-- title:
--   SoficGroups.KunActualSoficRootRadius.chosen_symmetric_wordEvaluation_generator
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

theorem SoficGroups.KunActualSoficRootRadius.chosen_symmetric_wordEvaluation_generator
    {G : Type*} [Group G] [DecidableEq G]
    (A : SoficGroups.SoficApproximation G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (n : ℕ) (i : ↥S) :
    chosenWordEvaluation A (fun j : ↥S => (j : G))
      (symmetricGeneratorWord S hsymmetric hgenerates)
      n (i : G) =
        (A.model n).action (i : G) := by sorry
