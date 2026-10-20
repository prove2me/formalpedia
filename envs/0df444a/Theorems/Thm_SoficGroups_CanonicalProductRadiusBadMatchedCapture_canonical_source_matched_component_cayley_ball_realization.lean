-- Prove2me | Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_canonical_source_matched_component_cayley_ball_realization
-- name    : SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonical_source_matched_component_cayley_ball_realization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/df4083ab-b4c4-449f-bd1a-02bccfbf56f6
-- title:
--   SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonical_source_matched_component_cayley_ball_realization
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

theorem SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonical_source_matched_component_cayley_ball_realization
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K) (honeS : 1 ∈ S)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (n k : ℕ)
    {U : Finset (Fin (A.model n).size)}
    (P : Finpartition U)
    (C : Finset (Fin (A.model n).size))
    (hC : C ∈ P.parts)
    (x : Fin (A.model n).size) (hx : x ∈ C)
    (hgood : x ∉
      SoficGroups.matchedRadiusBad
        P (sourceProductRadiusLabels S F k)
        ((A.model n).action)
        (canonicalProductRadiusBad
          A S hsymmetric hgenerates F n k)) :
    ∃ f : K → Fin (A.model n).size,
      Set.MapsTo f
        (↑(S ^ (k / 2)) : Set K)
        (↑C : Set (Fin (A.model n).size)) ∧
      Set.InjOn f (↑(S ^ (k / 2)) : Set K) := by sorry
