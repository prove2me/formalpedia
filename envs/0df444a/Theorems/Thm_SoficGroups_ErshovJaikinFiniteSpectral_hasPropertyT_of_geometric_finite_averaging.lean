-- Prove2me | Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_hasPropertyT_of_geometric_finite_averaging
-- name    : SoficGroups.ErshovJaikinFiniteSpectral.hasPropertyT_of_geometric_finite_averaging
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/2579c3fb-6a8c-41ea-94df-0368f22fb68b
-- title:
--   SoficGroups.ErshovJaikinFiniteSpectral.hasPropertyT_of_geometric_finite_averaging
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ErshovJaikinFiniteSpectral
open Filter Topology
universe u v

theorem SoficGroups.ErshovJaikinFiniteSpectral.hasPropertyT_of_geometric_finite_averaging
    {G : Type u} [Group G] (S : Finset G) (q : ℝ)
    (hq1 : q < 1)
    (haverage :
      ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] (π : SoficGroups.UnitaryRepresentation G H),
        ∃ A : H →L[ℂ] H,
          (∀ (x : H) (n : ℕ),
            dist ((A : H → H)^[n] x)
                ((A : H → H)^[n + 1] x) ≤
              (∑ g ∈ S, ‖π g x - x‖) * q ^ n) ∧
          (∀ x : H, A x = x → ∀ g : G, π g x = x)) :
    SoficGroups.HasPropertyT.{u, v} G := by sorry
