-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_transpose_boundary1_single_le
-- name    : QEC.Coding.FiberBundle.HammingWeight_transpose_boundary1_single_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:23:48.888438+00:00
-- url     : https://prove2.me/theorems/0f91c5a4-1d0f-4619-a629-cd6fd4744949
-- title:
--   Fiber Bundle: Hamming Weight transpose boundary1 single le
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight transpose boundary1 single le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L286-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L286-L326

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

theorem QEC.Coding.FiberBundle.HammingWeight_transpose_boundary1_single_le
    {B F : Nat}
    (a : baseZero) (i : fiberZero)
    (hBase : HammingWeight (fun b => D.baseBoundary a b) ≤ B)
    (hFiber : HammingWeight (fun j => D.fiberBoundary i j) ≤ F) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 D) (Pi.single (a, i) 1)) ≤
      B + F := by sorry
