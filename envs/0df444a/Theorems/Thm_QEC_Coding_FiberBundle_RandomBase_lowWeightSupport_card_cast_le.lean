-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_lowWeightSupport_card_cast_le
-- name    : QEC.Coding.FiberBundle.RandomBase.lowWeightSupport_card_cast_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:43:51.571485+00:00
-- url     : https://prove2.me/theorems/be22e3f3-dc61-49b1-9bb2-3b17c2e31d4e
-- title:
--   Random Base: low Weight Support card cast le
-- statement:
--   Weighted binomial count for all supports below the source's `0.2 n` cutoff.
--   This is an elementary entropy bound with the rational test weight `1/3`;
--   the floor is kept explicit, so no real-entropy approximation is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L685-L755
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L685-L755

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.lowWeightSupport_card_cast_le
    (r : Nat) :
    (Fintype.card (LowWeightSupport r) : ENNReal) ≤
      (3 : ENNReal) ^ ((4 * r) / 5) *
        ((4 : ENNReal) / 3) ^ (4 * r) := by sorry
