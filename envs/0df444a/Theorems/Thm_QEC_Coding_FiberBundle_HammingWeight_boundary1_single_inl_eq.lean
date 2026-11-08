-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary1_single_inl_eq
-- name    : QEC.Coding.FiberBundle.HammingWeight_boundary1_single_inl_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:38:35.227711+00:00
-- url     : https://prove2.me/theorems/62803137-a5ca-4a8c-b56c-6e795fe0ec0c
-- title:
--   Fiber Bundle: Hamming Weight boundary1 single inl eq
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight boundary1 single inl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L369-L377
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L369-L377

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

theorem QEC.Coding.FiberBundle.HammingWeight_boundary1_single_inl_eq
    (b : baseOne) (j : fiberZero) :
    HammingWeight (boundary1 D (Pi.single (Sum.inl (b, j)) 1)) =
      HammingWeight (fun a => D.baseBoundary a b) := by sorry
