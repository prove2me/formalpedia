-- Prove2me | Theorems.Thm_RH_Transport_SupportedMass_half_decay_exponent_nonpos
-- name    : RH.Transport.SupportedMass.half_decay_exponent_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:51.127181+00:00
-- url     : https://prove2.me/theorems/0e65f72a-f8ab-46a8-bc6a-7f2ab00a34ee
-- title:
--   Supported Mass: half decay exponent nonpos
-- statement:
--   The Supported Mass construction uses the half decay exponent nonpos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L159-L163
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L159-L163

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem RH.Transport.SupportedMass.half_decay_exponent_nonpos {p d : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) :
    -d / 2 + max 0 (5 * Geometry.ell p - 1 + d) / 8 ≤ 0 := by sorry
