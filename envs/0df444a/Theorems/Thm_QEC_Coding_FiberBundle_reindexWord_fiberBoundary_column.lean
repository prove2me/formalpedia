-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_reindexWord_fiberBoundary_column
-- name    : QEC.Coding.FiberBundle.reindexWord_fiberBoundary_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:05:19.465942+00:00
-- url     : https://prove2.me/theorems/bbd64d1a-d8bf-4d09-a889-2c7e31776dd7
-- title:
--   Fiber Bundle: reindex Word fiber Boundary column
-- statement:
--   Fiber naturality transports a boundary column through a cellular fiber
--   automorphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L366-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReduction.lean#L366-L373

import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_InitialCode
import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
omit [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [DecidableEq fiberZero] [DecidableEq fiberOne]

theorem QEC.Coding.FiberBundle.reindexWord_fiberBoundary_column
    (P : FiberAutomorphism fiberZero fiberOne D.fiberBoundary)
    (j : fiberOne) :
    reindexWord P.onZero (fun i => D.fiberBoundary i j) =
      fun i => D.fiberBoundary i (P.onOne j) := by sorry
