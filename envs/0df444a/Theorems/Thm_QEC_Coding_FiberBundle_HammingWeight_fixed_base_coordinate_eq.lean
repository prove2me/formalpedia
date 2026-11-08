-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_fixed_base_coordinate_eq
-- name    : QEC.Coding.FiberBundle.HammingWeight_fixed_base_coordinate_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:18:40.403711+00:00
-- url     : https://prove2.me/theorems/b5fcc1e5-a326-46b0-b079-0c91c74f342d
-- title:
--   Fiber Bundle: Hamming Weight fixed base coordinate eq
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight fixed base coordinate eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L140-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L140-L178

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

theorem QEC.Coding.FiberBundle.HammingWeight_fixed_base_coordinate_eq
    {F B I : Type*} [Zero F] [DecidableEq F]
    [Fintype B] [DecidableEq B] [Fintype I]
    (b : B) (y : Word F I) :
    HammingWeight
        (fun p : B × I => if b = p.1 then y p.2 else 0) =
      HammingWeight y := by sorry
