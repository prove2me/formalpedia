-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_chainComplexBoundaryIncidence_weightReducedData_variableSupport_le_five
-- name    : QEC.Coding.FiberBundle.chainComplexBoundaryIncidence_weightReducedData_variableSupport_le_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:27:26.209134+00:00
-- url     : https://prove2.me/theorems/df2a2b34-5530-418c-a77e-73386091636e
-- title:
--   Fiber Bundle: chain Complex Boundary Incidence weight Reduced Data variable Support le five
-- statement:
--   The Fiber Bundle construction uses the chain Complex Boundary Incidence weight Reduced Data variable Support le five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L676-L689
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionParameters.lean#L676-L689

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

theorem QEC.Coding.FiberBundle.chainComplexBoundaryIncidence_weightReducedData_variableSupport_le_five
    (q : QubitIndex
      (ClassicalWeightReduction.WeightReducedCheck R)
      (ClassicalWeightReduction.WeightReducedBit R)
      fiberZero fiberOne)
    (hFiberRow : ∀ i : fiberZero,
      HammingWeight (fun j => D.fiberBoundary i j) ≤ 2)
    (hFiberCol : ∀ j : fiberOne,
      HammingWeight (fun i => D.fiberBoundary i j) ≤ 2) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence
      (chainComplex (weightReducedData D))).variableSupport q).card ≤ 5 := by sorry
