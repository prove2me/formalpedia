-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_graph_coordinate_eq
-- name    : QEC.Coding.FiberBundle.HammingWeight_graph_coordinate_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:19:16.998596+00:00
-- url     : https://prove2.me/theorems/0f84bcd2-7fd6-4fac-b8e4-00e971d30cef
-- title:
--   Fiber Bundle: Hamming Weight graph coordinate eq
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight graph coordinate eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L180-L217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L180-L217

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

theorem QEC.Coding.FiberBundle.HammingWeight_graph_coordinate_eq
    {F B I : Type*} [Zero F] [DecidableEq F]
    [Fintype B] [Fintype I] [DecidableEq I]
    (x : Word F B) (psi : B → I) :
    HammingWeight
        (fun p : B × I => if p.2 = psi p.1 then x p.1 else 0) =
      HammingWeight x := by sorry
