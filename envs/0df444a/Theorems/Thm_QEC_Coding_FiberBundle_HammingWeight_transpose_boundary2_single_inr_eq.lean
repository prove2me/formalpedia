-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_transpose_boundary2_single_inr_eq
-- name    : QEC.Coding.FiberBundle.HammingWeight_transpose_boundary2_single_inr_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:39:39.107413+00:00
-- url     : https://prove2.me/theorems/b83feedf-0a8b-417c-a56f-d2835830fe1a
-- title:
--   Fiber Bundle: Hamming Weight transpose boundary2 single inr eq
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight transpose boundary2 single inr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L404-L419
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L404-L419

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

theorem QEC.Coding.FiberBundle.HammingWeight_transpose_boundary2_single_inr_eq
    (a : baseZero) (j : fiberOne) :
    HammingWeight
        (wordLinearMapTranspose (boundary2 D)
          (Pi.single (Sum.inr (a, j)) 1)) =
      HammingWeight (fun b => D.baseBoundary a b) := by sorry
