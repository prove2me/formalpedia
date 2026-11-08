-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_weightReductionForwardMap1_lipschitz
-- name    : QEC.Coding.FiberBundle.weightReductionForwardMap1_lipschitz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:15:58.355657+00:00
-- url     : https://prove2.me/theorems/a0475f11-188a-42dc-b39f-456683d73938
-- title:
--   Fiber Bundle: weight Reduction Forward Map1 lipschitz
-- statement:
--   The concrete HHO20 bundle forward map loses at most the maximum original
--   bit degree in Hamming weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L281-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L281-L299

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

theorem QEC.Coding.FiberBundle.weightReductionForwardMap1_lipschitz
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {L : Nat} (hOne : 1 ≤ L)
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L)
    (x : Word (ZMod 2)
      (QubitIndex
        (ClassicalWeightReduction.WeightReducedCheck R)
        (ClassicalWeightReduction.WeightReducedBit R)
        fiberZero fiberOne)) :
    HammingWeight (weightReductionForwardMap1 D h x) ≤
      L * HammingWeight x := by sorry
