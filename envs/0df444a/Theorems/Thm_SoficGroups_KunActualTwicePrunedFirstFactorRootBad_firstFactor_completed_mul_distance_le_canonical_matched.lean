-- Prove2me | Theorems.Thm_SoficGroups_KunActualTwicePrunedFirstFactorRootBad_firstFactor_completed_mul_distance_le_canonical_matched
-- name    : SoficGroups.KunActualTwicePrunedFirstFactorRootBad.firstFactor_completed_mul_distance_le_canonical_matched
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/6c858448-efc4-49d8-bb9d-f36d3604b0f7
-- title:
--   SoficGroups.KunActualTwicePrunedFirstFactorRootBad.firstFactor_completed_mul_distance_le_canonical_matched
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

theorem SoficGroups.KunActualTwicePrunedFirstFactorRootBad.firstFactor_completed_mul_distance_le_canonical_matched
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (n k : ℕ)
    {U : Finset (Fin (A.model n).size)}
    (Q : Finpartition U)
    (C : Finset (Fin (A.model n).size))
    (hC : C ∈ Q.parts)
    (a g : K)
    (ha : a ∈ S ^ k) (hg : g ∈ S ^ k)
    (hag : a * g ∈ S ^ k) :
    SoficGroups.permutationDistance
        (completedRestriction
          ((A.model n).action (a * g, (1 : J))) C)
        (completedRestriction
          ((A.model n).action (a, (1 : J))) C *
         completedRestriction
          ((A.model n).action (g, (1 : J))) C) ≤
      (C ∩ SoficGroups.matchedRadiusBad
        Q (sourceProductRadiusLabels S F k)
        ((A.model n).action)
        (canonicalProductRadiusBad A S hsymmetric hgenerates F n k)).card := by sorry
