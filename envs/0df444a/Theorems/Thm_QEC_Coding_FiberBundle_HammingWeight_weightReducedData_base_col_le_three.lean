-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_weightReducedData_base_col_le_three
-- name    : QEC.Coding.FiberBundle.HammingWeight_weightReducedData_base_col_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:19:40.0444+00:00
-- url     : https://prove2.me/theorems/929dc894-5693-4176-8b54-544637d0ff1c
-- title:
--   Fiber Bundle: Hamming Weight weight Reduced Data base col le three
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight weight Reduced Data base col le three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L440-L448
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L440-L448

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

theorem QEC.Coding.FiberBundle.HammingWeight_weightReducedData_base_col_le_three
    (b : ClassicalWeightReduction.WeightReducedBit R) :
    HammingWeight
        (fun q => (weightReducedData D).baseBoundary q b) ≤ 3 := by sorry
