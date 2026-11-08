-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
-- name    : QEC.Coding.FiberBundle.chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:18:45.653219+00:00
-- url     : https://prove2.me/theorems/e600fee6-b390-4f4f-a415-ff338173fa77
-- title:
--   Fiber Bundle: chain Complex Boundary Incidence variable Support card eq boundary columns
-- statement:
--   The Fiber Bundle construction uses the chain Complex Boundary Incidence variable Support card eq boundary columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L254-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L254-L284

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns

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

theorem QEC.Coding.FiberBundle.chainComplexBoundaryIncidence_variableSupport_card_eq_boundary_columns
    {F : Type u} {I K L : Type v} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [Fintype K] [Fintype L]
    (C : ChainComplexData F (Word F K) (Word F I) (Word F L)) (q : I) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence C).variableSupport q).card =
      HammingWeight
        (C.boundary1 (canonicalBasisWord (F := F) q)) +
      HammingWeight
        (wordLinearMapTranspose C.boundary2
          (canonicalBasisWord (F := F) q)) := by sorry
