-- Prove2me | Theorems.Thm_RH_Transport_SupportedMass_finite_scaled_supported_mass_le
-- name    : RH.Transport.SupportedMass.finite_scaled_supported_mass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:57:12.269198+00:00
-- url     : https://prove2.me/theorems/5ad3832d-4007-4cc3-b664-4dffa901ea48
-- title:
--   Supported Mass: finite scaled supported mass le
-- statement:
--   The Supported Mass construction uses the finite scaled supported mass le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L76-L84
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L76-L84

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem RH.Transport.SupportedMass.finite_scaled_supported_mass_le {ι : Type*} (F : Finset ι)
    (q : ι → ℝ) {a Z : ℝ} (ha : 0 < a) (hZ : 0 < Z) (ell : ℝ)
    (hsupport : ∀ i ∈ F, a * Z ^ ell ≤ q i) :
    (∑ i ∈ F, q i ^ (-2 : ℝ)) ≤
      (a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell / 2)) *
        ∑ i ∈ F, q i ^ (-(3 / 2 : ℝ)) := by sorry
