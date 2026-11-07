-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_add_bundleCoboundary_mem_middleCocycleCode_iff
-- name    : QEC.Coding.FiberBundle.add_bundleCoboundary_mem_middleCocycleCode_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:05:21.242837+00:00
-- url     : https://prove2.me/theorems/9ba3bf68-d8fa-49c0-bb3d-3c532a25d137
-- title:
--   Fiber Bundle: add bundle Coboundary mem middle Cocycle Code iff
-- statement:
--   Adding a bundle coboundary preserves the cocycle condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1359-L1372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1359-L1372

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.add_bundleCoboundary_mem_middleCocycleCode_iff
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    x + bundleCoboundary D u ∈ (chainComplex D).middleCocycleCode.carrier ↔
      x ∈ (chainComplex D).middleCocycleCode.carrier := by sorry
