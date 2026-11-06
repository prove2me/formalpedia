-- Prove2me | Theorems.Thm_RH_Transport_SupportedMass_weighted_mass_decay
-- name    : RH.Transport.SupportedMass.weighted_mass_decay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:46.601462+00:00
-- url     : https://prove2.me/theorems/61edc924-0ad2-4302-9256-4cd54d98aa3f
-- title:
--   Supported Mass: weighted mass decay
-- statement:
--   A bounded three-halves mass gives an actual scale-decaying weighted sum.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L87-L104
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L87-L104

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem RH.Transport.SupportedMass.weighted_mass_decay {ι : Type*} (F : Finset ι)
    (q w : ι → ℝ) {a Z C ell : ℝ}
    (ha : 0 < a) (hZ : 0 < Z)
    (hw : ∀ i ∈ F, 0 ≤ w i)
    (hsupport : ∀ i ∈ F, w i ≠ 0 → a * Z ^ ell ≤ q i)
    (hmass : (∑ i ∈ F, w i * q i ^ (-(3 / 2 : ℝ))) ≤ C) :
    (∑ i ∈ F, w i * q i ^ (-2 : ℝ)) ≤
      (C * a ^ (-(1 / 2 : ℝ))) * Z ^ (-ell / 2) := by sorry
