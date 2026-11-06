-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_c0Fiber_eq_zero_of_not_mem_c0Shadow
-- name    : QEC.Coding.FiberBundle.c0Fiber_eq_zero_of_not_mem_c0Shadow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:52:26.612214+00:00
-- url     : https://prove2.me/theorems/c032d2fb-ac58-44cc-911d-7aa8d5084219
-- title:
--   Fiber Bundle: c0 Fiber eq zero of not mem c0 Shadow
-- statement:
--   Outside its zero-cell shadow, a total-degree-zero fiber word vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L121-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L121-L128

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.c0Fiber_eq_zero_of_not_mem_c0Shadow
    {baseZero fiberZero : Type u}
    [Fintype baseZero] [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    {a : baseZero} (ha : a ∉ c0Shadow u) :
    c0Fiber u a = 0 := by sorry
