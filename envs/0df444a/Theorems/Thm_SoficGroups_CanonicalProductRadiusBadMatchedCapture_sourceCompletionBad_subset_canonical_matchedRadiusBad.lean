-- Prove2me | Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_sourceCompletionBad_subset_canonical_matchedRadiusBad
-- name    : SoficGroups.CanonicalProductRadiusBadMatchedCapture.sourceCompletionBad_subset_canonical_matchedRadiusBad
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/7ab46e45-9f9d-465b-a3c2-d1970e3353e7
-- title:
--   SoficGroups.CanonicalProductRadiusBadMatchedCapture.sourceCompletionBad_subset_canonical_matchedRadiusBad
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.ChosenCayleyMatchedComponentRealization
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open scoped BigOperators Pointwise symmDiff

theorem SoficGroups.CanonicalProductRadiusBadMatchedCapture.sourceCompletionBad_subset_canonical_matchedRadiusBad
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (n k : ℕ)
    {U : Finset (Fin (A.model n).size)}
    (P : Finpartition U)
    (C : Finset (Fin (A.model n).size))
    (hC : C ∈ P.parts) :
    sourceCompletionBad
      (fun i : ↥S => (A.model n).action ((i : K), 1))
      (fun j : J => (A.model n).action (1, j))
      F C ⊆
      C ∩ SoficGroups.matchedRadiusBad
        P (sourceProductRadiusLabels S F k)
        ((A.model n).action)
        (canonicalProductRadiusBad
          A S hsymmetric hgenerates F n k) := by sorry
