-- Prove2me | Theorems.Thm_SoficGroups_KunActualTwicePrunedFirstFactorRootBad_completedRestriction_mul_distance_le_failure_add_deleted
-- name    : SoficGroups.KunActualTwicePrunedFirstFactorRootBad.completedRestriction_mul_distance_le_failure_add_deleted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/2bdfe777-e133-49a6-bee0-9b9a747dbe8c
-- title:
--   SoficGroups.KunActualTwicePrunedFirstFactorRootBad.completedRestriction_mul_distance_le_failure_add_deleted
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualTwicePrunedFirstFactorRootBad
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open scoped BigOperators Pointwise

theorem SoficGroups.KunActualTwicePrunedFirstFactorRootBad.completedRestriction_mul_distance_le_failure_add_deleted
    {V : Type*} [Fintype V] [DecidableEq V]
    (p q r : Equiv.Perm V) (Z : Finset V) :
    SoficGroups.permutationDistance
        (completedRestriction r Z)
        (completedRestriction p Z * completedRestriction q Z) ≤
      (Finset.univ.filter fun x : V => r x ≠ p (q x)).card +
        2 * (Finset.univ \ Z).card := by sorry
