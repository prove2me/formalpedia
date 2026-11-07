-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_lowWeightSupport_card_le
-- name    : QEC.Coding.FiberBundle.RandomBase.lowWeightSupport_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:43:48.234188+00:00
-- url     : https://prove2.me/theorems/dbe5561b-5c62-4856-8af0-51bf2eb7fbb3
-- title:
--   Random Base: low Weight Support card le
-- statement:
--   Every source-low-weight support has cardinality at most `⌊4r/5⌋`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L673-L678
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/Distance.lean#L673-L678

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.lowWeightSupport_card_le
    {r : Nat} (A : LowWeightSupport r) :
    A.1.card ≤ (4 * r) / 5 := by sorry
