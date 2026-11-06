-- Prove2me | Theorems.Thm_RH_Transport_SupportedMass_uniform_mass_bound_gives_decay
-- name    : RH.Transport.SupportedMass.uniform_mass_bound_gives_decay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:57:10.422433+00:00
-- url     : https://prove2.me/theorems/436be00a-cc74-45f0-b058-c50e8e3a55f5
-- title:
--   Supported Mass: uniform mass bound gives decay
-- statement:
--   Direct interface for a supplied uniform finite three-halves mass bound.
--   For supported ideals, the source theorem at exponent -3/2 has exactly this
--   form. This theorem itself is valid for any index type and real norm function.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L109-L122
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L109-L122

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem RH.Transport.SupportedMass.uniform_mass_bound_gives_decay {ι : Type*} (q : ι → ℝ)
    (hbase : ∃ C : ℝ, 0 < C ∧ ∀ F : Finset ι,
      (∑ i ∈ F, q i ^ (-(3 / 2 : ℝ))) ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Finset ι) (a Z ell : ℝ),
      0 < a → 0 < Z → (∀ i ∈ F, a * Z ^ ell ≤ q i) →
      (∑ i ∈ F, q i ^ (-2 : ℝ)) ≤
        (C * a ^ (-(1 / 2 : ℝ))) * Z ^ (-ell / 2) := by sorry
