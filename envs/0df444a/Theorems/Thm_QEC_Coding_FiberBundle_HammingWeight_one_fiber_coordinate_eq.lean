-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_one_fiber_coordinate_eq
-- name    : QEC.Coding.FiberBundle.HammingWeight_one_fiber_coordinate_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:18:32.495733+00:00
-- url     : https://prove2.me/theorems/f9c2b15d-8d5d-41fd-9bc8-def826821688
-- title:
--   Fiber Bundle: Hamming Weight one fiber coordinate eq
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight one fiber coordinate eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L100-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L100-L138

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

theorem QEC.Coding.FiberBundle.HammingWeight_one_fiber_coordinate_eq
    {F B I : Type*} [Zero F] [DecidableEq F]
    [Fintype B] [Fintype I] [DecidableEq I]
    (x : Word F B) (phi : B → Equiv.Perm I) (i : I) :
    HammingWeight
        (fun p : B × I => if i = phi p.1 p.2 then x p.1 else 0) =
      HammingWeight x := by sorry
