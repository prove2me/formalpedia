-- Prove2me | Theorems.Thm_SoficGroups_ChosenCayleyMatchedComponentRealization_sourceFirstFactor_injective_ball
-- name    : SoficGroups.ChosenCayleyMatchedComponentRealization.sourceFirstFactor_injective_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/f7d9a249-0aba-4273-a825-76a3bcdaba51
-- title:
--   SoficGroups.ChosenCayleyMatchedComponentRealization.sourceFirstFactor_injective_ball
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

theorem SoficGroups.ChosenCayleyMatchedComponentRealization.sourceFirstFactor_injective_ball
    {K J : Type*} [Group K] [Group J] [DecidableEq K]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (n k : ℕ)
    {x : Fin (A.model n).size}
    (hx : x ∉ sourceFirstFactorCayleyRadiusBad
      A S hsymmetric hgenerates n k) :
    Set.InjOn
      (fun g : K => (A.model n).action (g, 1) x)
      (↑(S ^ k) : Set K) := by sorry
