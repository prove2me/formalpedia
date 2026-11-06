-- Prove2me | Theorems.Thm_RH_Transport_LocalBounds_goodTailDecay_eq
-- name    : RH.Transport.LocalBounds.goodTailDecay_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:56:56.87751+00:00
-- url     : https://prove2.me/theorems/a1b6b5e9-1870-4d9e-a575-b756138a12a0
-- title:
--   Local Bounds: good Tail Decay eq
-- statement:
--   The Local Bounds construction uses the good Tail Decay eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L162-L165
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/LocalBounds.lean#L162-L165

import Definitions.Def_Transport_Geometry
import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
open RH RH.Transport RH.Transport.LocalBounds
open RH.Transport.Geometry
noncomputable section

theorem RH.Transport.LocalBounds.goodTailDecay_eq (p : ℝ) :
    goodTailDecay p = -1 - goodCap p := by sorry
