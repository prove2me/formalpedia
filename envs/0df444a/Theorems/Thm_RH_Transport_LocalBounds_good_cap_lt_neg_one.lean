-- Prove2me | Theorems.Thm_RH_Transport_LocalBounds_good_cap_lt_neg_one
-- name    : RH.Transport.LocalBounds.good_cap_lt_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:37.076397+00:00
-- url     : https://prove2.me/theorems/e2e258a4-e24f-4a5a-af4a-ff25a88f8967
-- title:
--   Local Bounds: good cap lt neg one
-- statement:
--   The Local Bounds construction uses the good cap lt neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L76-L79
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L76-L79

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem RH.Transport.LocalBounds.good_cap_lt_neg_one {p : ℝ} (hp : p < 1 / 1000) :
    goodCap p < -1 := by sorry
