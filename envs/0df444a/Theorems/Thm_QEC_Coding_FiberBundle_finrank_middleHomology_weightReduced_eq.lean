-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_finrank_middleHomology_weightReduced_eq
-- name    : QEC.Coding.FiberBundle.finrank_middleHomology_weightReduced_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:15:07.809642+00:00
-- url     : https://prove2.me/theorems/9177fe0c-2fb7-45d2-99ed-8f8c0afbf241
-- title:
--   Fiber Bundle: finrank middle Homology weight Reduced eq
-- statement:
--   Weight reduction preserves the number of encoded logical qubits exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L30-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L30-L35

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D

theorem QEC.Coding.FiberBundle.finrank_middleHomology_weightReduced_eq
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R) :
    Module.finrank (ZMod 2)
        (chainComplex (weightReducedData D)).middleHomology =
      Module.finrank (ZMod 2) (chainComplex D).middleHomology := by sorry
