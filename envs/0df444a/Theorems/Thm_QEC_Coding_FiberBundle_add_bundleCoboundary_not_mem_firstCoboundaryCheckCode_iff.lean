-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_add_bundleCoboundary_not_mem_firstCoboundaryCheckCode_iff
-- name    : QEC.Coding.FiberBundle.add_bundleCoboundary_not_mem_firstCoboundaryCheckCode_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:30:20.833229+00:00
-- url     : https://prove2.me/theorems/8b1bd2b1-c929-4dd8-9ba7-f3debd2a30ab
-- title:
--   Fiber Bundle: add bundle Coboundary not mem first Coboundary Check Code iff
-- statement:
--   Adding a bundle coboundary preserves nontriviality of a cohomology class.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1375-L1389
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/CohomologyDistance.lean#L1375-L1389

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u

theorem QEC.Coding.FiberBundle.add_bundleCoboundary_not_mem_firstCoboundaryCheckCode_iff
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (x : Word (ZMod 2) (QubitIndex baseZero baseOne fiberZero fiberOne))
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    x + bundleCoboundary D u ∉
        (chainComplex D).firstCoboundaryCheckCode.carrier ↔
      x ∉ (chainComplex D).firstCoboundaryCheckCode.carrier := by sorry
