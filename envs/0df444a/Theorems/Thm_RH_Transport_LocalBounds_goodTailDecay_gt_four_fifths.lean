-- Prove2me | Theorems.Thm_RH_Transport_LocalBounds_goodTailDecay_gt_four_fifths
-- name    : RH.Transport.LocalBounds.goodTailDecay_gt_four_fifths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:57:08.250989+00:00
-- url     : https://prove2.me/theorems/15dadb2f-dfa3-4588-8663-892f2fef12e7
-- title:
--   Local Bounds: good Tail Decay gt four fifths
-- statement:
--   The Local Bounds construction uses the good Tail Decay gt four fifths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L167-L170
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L167-L170

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem RH.Transport.LocalBounds.goodTailDecay_gt_four_fifths {p : ℝ} (hp : p < 1 / 1000) :
    (4 / 5 : ℝ) < goodTailDecay p := by sorry
