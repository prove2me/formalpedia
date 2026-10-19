-- Prove2me | Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_canonicalProductRadiusBad_density_tendsto_zero
-- name    : SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad_density_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/4617af67-4f02-40cc-9406-145ddfdb32ce
-- title:
--   SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad_density_tendsto_zero
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

theorem SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad_density_tendsto_zero
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (k : ℕ) :
    Tendsto
      (fun n =>
        ((canonicalProductRadiusBad
          A S hsymmetric hgenerates F n k).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) := by sorry
