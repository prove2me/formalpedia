-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_sourceHomologySlice_ne_zero_iff
-- name    : QEC.Coding.DistanceBalancing.sourceHomologySlice_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:18:05.790464+00:00
-- url     : https://prove2.me/theorems/746a00d4-58a0-4e4a-8f4f-973f12193e24
-- title:
--   Distance Balancing: source Homology Slice ne zero iff
-- statement:
--   The Distance Balancing construction uses the source Homology Slice ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L881-L898
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L881-L898

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)

theorem QEC.Coding.DistanceBalancing.sourceHomologySlice_ne_zero_iff
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (a : classicalBit) :
    sourceHomologySlice D z hz a ≠ 0 ↔
      xOneBitSlice z a ∉
        (sourceChainComplex D).middleBoundaryCode.carrier := by sorry
