-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_boundary1_single_inr_eq
-- name    : QEC.Coding.FiberBundle.HammingWeight_boundary1_single_inr_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:38:46.964955+00:00
-- url     : https://prove2.me/theorems/f7a9d242-1c6e-43d3-ac9d-b4bef7aa6268
-- title:
--   Fiber Bundle: Hamming Weight boundary1 single inr eq
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight boundary1 single inr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L379-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L379-L387

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

theorem QEC.Coding.FiberBundle.HammingWeight_boundary1_single_inr_eq
    (a : baseZero) (j : fiberOne) :
    HammingWeight (boundary1 D (Pi.single (Sum.inr (a, j)) 1)) =
      HammingWeight (fun i => D.fiberBoundary i j) := by sorry
