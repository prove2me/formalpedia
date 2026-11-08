-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_productVariableSupport_card_eq_boundaryColumnWeight
-- name    : QEC.Coding.DistanceBalancing.productVariableSupport_card_eq_boundaryColumnWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:26:22.046843+00:00
-- url     : https://prove2.me/theorems/5ac5f31b-bfea-4589-bff5-24db3927a93a
-- title:
--   Distance Balancing: product Variable Support card eq boundary Column Weight
-- statement:
--   Exact product variable degree in terms of its two boundary columns.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L267-L276
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L267-L276

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open QEC.Coding.FiberBundle
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

theorem QEC.Coding.DistanceBalancing.productVariableSupport_card_eq_boundaryColumnWeight
    (q : QubitIndex xOne xTwo classicalBit classicalCheck) :
    ((QEC.QLDPC.chainComplexBoundaryIncidence (chainComplex D)).variableSupport q).card =
      HammingWeight (boundary1 D (canonicalBasisWord (F := ZMod 2) q)) +
        HammingWeight
          (wordLinearMapTranspose (boundary2 D)
            (canonicalBasisWord (F := ZMod 2) q)) := by sorry
