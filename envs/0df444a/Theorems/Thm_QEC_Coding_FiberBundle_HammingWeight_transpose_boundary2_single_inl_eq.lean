-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_transpose_boundary2_single_inl_eq
-- name    : QEC.Coding.FiberBundle.HammingWeight_transpose_boundary2_single_inl_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:39:17.97211+00:00
-- url     : https://prove2.me/theorems/e11c29bb-568b-45df-9f21-591134cd0082
-- title:
--   Fiber Bundle: Hamming Weight transpose boundary2 single inl eq
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight transpose boundary2 single inl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L389-L402
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L389-L402

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

theorem QEC.Coding.FiberBundle.HammingWeight_transpose_boundary2_single_inl_eq
    (b : baseOne) (i : fiberZero) :
    HammingWeight
        (wordLinearMapTranspose (boundary2 D)
          (Pi.single (Sum.inl (b, i)) 1)) =
      HammingWeight (fun j => D.fiberBoundary i j) := by sorry
