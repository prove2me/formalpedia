-- Prove2me | Theorems.Thm_RH_Transport_SupportedMass_finite_weighted_supported_mass_le
-- name    : RH.Transport.SupportedMass.finite_weighted_supported_mass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:39.410547+00:00
-- url     : https://prove2.me/theorems/fe06e88a-8e2a-4840-b0bd-4697c5b8f6d3
-- title:
--   Supported Mass: finite weighted supported mass le
-- statement:
--   The threshold is required only at points where the weight is nonzero.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L49-L65
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L49-L65

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem RH.Transport.SupportedMass.finite_weighted_supported_mass_le {ι : Type*} (F : Finset ι)
    (q w : ι → ℝ) {T : ℝ} (hT : 0 < T)
    (hw : ∀ i ∈ F, 0 ≤ w i)
    (hsupport : ∀ i ∈ F, w i ≠ 0 → T ≤ q i) :
    (∑ i ∈ F, w i * q i ^ (-2 : ℝ)) ≤
      T ^ (-(1 / 2 : ℝ)) *
        ∑ i ∈ F, w i * q i ^ (-(3 / 2 : ℝ)) := by sorry
