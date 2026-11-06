-- Prove2me | Theorems.Thm_RH_Transport_SupportedMass_finite_supported_mass_le
-- name    : RH.Transport.SupportedMass.finite_supported_mass_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:45.09932+00:00
-- url     : https://prove2.me/theorems/afb964ea-3db3-4d7a-b7d0-e0678ad4ea90
-- title:
--   Supported Mass: finite supported mass le
-- statement:
--   The Supported Mass construction uses the finite supported mass le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L38-L46
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L38-L46

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem RH.Transport.SupportedMass.finite_supported_mass_le {ι : Type*} (F : Finset ι)
    (q : ι → ℝ) {T : ℝ} (hT : 0 < T)
    (hsupport : ∀ i ∈ F, T ≤ q i) :
    (∑ i ∈ F, q i ^ (-2 : ℝ)) ≤
      T ^ (-(1 / 2 : ℝ)) * ∑ i ∈ F, q i ^ (-(3 / 2 : ℝ)) := by sorry
