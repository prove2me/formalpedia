-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_card_c0Shadow_eraseC0Fiber_lt
-- name    : QEC.Coding.FiberBundle.card_c0Shadow_eraseC0Fiber_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:19:39.751206+00:00
-- url     : https://prove2.me/theorems/6662e157-b116-43c6-a23d-68815c93964f
-- title:
--   Fiber Bundle: card c0 Shadow erase C0 Fiber lt
-- statement:
--   Erasing a supported fiber strictly decreases the shadow cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L543-L552
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L543-L552

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.card_c0Shadow_eraseC0Fiber_lt
    {baseZero fiberZero : Type u}
    [Fintype baseZero] [DecidableEq baseZero] [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    {a : baseZero} (ha : a ∈ c0Shadow u) :
    (c0Shadow (eraseC0Fiber u a)).card < (c0Shadow u).card := by sorry
