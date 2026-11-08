-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary2_single_le
-- name    : QEC.Coding.FiberBundle.HammingWeight_boundary2_single_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:24:27.545195+00:00
-- url     : https://prove2.me/theorems/dcaf5c8f-a8fb-4a48-b817-60d32b61bd26
-- title:
--   Fiber Bundle: Hamming Weight boundary2 single le
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight boundary2 single le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L329-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L329-L367

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u v
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
omit [DecidableEq baseZero] [DecidableEq fiberZero]

theorem QEC.Coding.FiberBundle.HammingWeight_boundary2_single_le
    {B F : Nat}
    (b : baseOne) (j : fiberOne)
    (hBase : HammingWeight (fun a => D.baseBoundary a b) ≤ B)
    (hFiber : HammingWeight (fun i => D.fiberBoundary i j) ≤ F) :
    HammingWeight (boundary2 D (Pi.single (b, j) 1)) ≤ F + B := by sorry
