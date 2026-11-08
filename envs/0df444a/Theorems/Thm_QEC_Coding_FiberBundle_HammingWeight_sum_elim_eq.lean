-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_sum_elim_eq
-- name    : QEC.Coding.FiberBundle.HammingWeight_sum_elim_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:18:16.871093+00:00
-- url     : https://prove2.me/theorems/b4ed3a43-4bef-4be4-84e1-a6f611794884
-- title:
--   Fiber Bundle: Hamming Weight sum elim eq
-- statement:
--   The Fiber Bundle construction uses the Hamming Weight sum elim eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L26-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L26-L54

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

theorem QEC.Coding.FiberBundle.HammingWeight_sum_elim_eq
    {F A B : Type*} [Zero F] [DecidableEq F]
    [Fintype A] [Fintype B]
    (x : Word F A) (y : Word F B) :
    HammingWeight (Sum.elim x y) =
      HammingWeight x + HammingWeight y := by sorry
