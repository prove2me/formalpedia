-- Prove2me | Theorems.Thm_SoficGroups_ChosenCayleyMatchedComponentRealization_sourceFirstFactorCayleyRadiusBad_density_tendsto_zero
-- name    : SoficGroups.ChosenCayleyMatchedComponentRealization.sourceFirstFactorCayleyRadiusBad_density_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/75c4dba8-209f-4d2f-8fa2-02d48fd2a6e5
-- title:
--   SoficGroups.ChosenCayleyMatchedComponentRealization.sourceFirstFactorCayleyRadiusBad_density_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ChosenCayleyMatchedComponentRealization
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunResidualRetainedSelection
open scoped BigOperators Pointwise symmDiff

theorem SoficGroups.ChosenCayleyMatchedComponentRealization.sourceFirstFactorCayleyRadiusBad_density_tendsto_zero
    {K J : Type*} [Group K] [Group J] [DecidableEq K]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (k : ℕ) :
    Tendsto
      (fun n =>
        ((sourceFirstFactorCayleyRadiusBad
          A S hsymmetric hgenerates n k).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) := by sorry
