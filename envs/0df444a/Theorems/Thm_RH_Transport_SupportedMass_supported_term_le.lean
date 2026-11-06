-- Prove2me | Theorems.Thm_RH_Transport_SupportedMass_supported_term_le
-- name    : RH.Transport.SupportedMass.supported_term_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:43.316198+00:00
-- url     : https://prove2.me/theorems/e2302144-697b-4726-9fc1-9c1db474c109
-- title:
--   Supported Mass: supported term le
-- statement:
--   The Supported Mass construction uses the supported term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L27-L36
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/SupportedMass.lean#L27-L36

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem RH.Transport.SupportedMass.supported_term_le {q T : ℝ} (hT : 0 < T) (hq : T ≤ q) :
    q ^ (-2 : ℝ) ≤ T ^ (-(1 / 2 : ℝ)) * q ^ (-(3 / 2 : ℝ)) := by sorry
