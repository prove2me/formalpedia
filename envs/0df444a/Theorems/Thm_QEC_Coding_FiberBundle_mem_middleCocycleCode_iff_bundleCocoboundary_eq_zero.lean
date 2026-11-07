-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero
-- name    : QEC.Coding.FiberBundle.mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:07:24.011052+00:00
-- url     : https://prove2.me/theorems/b2471964-7d9a-4cda-849c-9e96bf5a67be
-- title:
--   Fiber Bundle: mem middle Cocycle Code iff bundle Cocoboundary eq zero
-- statement:
--   Membership in the middle cocycle code is vanishing bundle cocoboundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L204-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyRepresentatives.lean#L204-L215

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.mem_middleCocycleCode_iff_bundleCocoboundary_eq_zero
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    z ∈ (chainComplex D).middleCocycleCode.carrier ↔
      bundleCocoboundary D z = 0 := by sorry
