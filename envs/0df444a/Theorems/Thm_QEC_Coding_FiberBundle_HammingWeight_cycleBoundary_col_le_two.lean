-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_cycleBoundary_col_le_two
-- name    : QEC.Coding.FiberBundle.HammingWeight_cycleBoundary_col_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:18:53.266553+00:00
-- url     : https://prove2.me/theorems/344decdd-f085-494f-a662-3bca0190e099
-- title:
--   Fiber Bundle: Hamming Weight cycle Boundary col le two
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight cycle Boundary col le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L81-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L81-L98

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

theorem QEC.Coding.FiberBundle.HammingWeight_cycleBoundary_col_le_two
    (n : Nat) [NeZero n] (j : ZMod n) :
    HammingWeight (fun i => cycleBoundary n i j) ≤ 2 := by sorry
