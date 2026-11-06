-- Prove2me | Theorems.Thm_RH_Transport_LocalBounds_denominator_cap_neg
-- name    : RH.Transport.LocalBounds.denominator_cap_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:28.706791+00:00
-- url     : https://prove2.me/theorems/ff62b0b5-2b81-4961-a4c0-b7e39de5b60c
-- title:
--   Local Bounds: denominator cap neg
-- statement:
--   The Local Bounds construction uses the denominator cap neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L45-L47
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L45-L47

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem RH.Transport.LocalBounds.denominator_cap_neg {p : ℝ} (hp : p < 1 / 1000)
    (term : DenominatorTerm) : denominatorCap term p < 0 := by sorry
