-- Prove2me | Theorems.Thm_RH_Transport_SupportedMass_threshold_power_identity
-- name    : RH.Transport.SupportedMass.threshold_power_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:45.662195+00:00
-- url     : https://prove2.me/theorems/717a0e0b-9c87-499d-88e6-ad9dd027525c
-- title:
--   Supported Mass: threshold power identity
-- statement:
--   The Supported Mass construction uses the threshold power identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L67-L74
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L67-L74

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem RH.Transport.SupportedMass.threshold_power_identity {a Z : ℝ} (ha : 0 < a) (hZ : 0 < Z)
    (ell : ℝ) :
    (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) =
      a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell / 2) := by sorry
