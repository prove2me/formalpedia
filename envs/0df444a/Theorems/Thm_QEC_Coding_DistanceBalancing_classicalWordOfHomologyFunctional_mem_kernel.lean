-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_classicalWordOfHomologyFunctional_mem_kernel
-- name    : QEC.Coding.DistanceBalancing.classicalWordOfHomologyFunctional_mem_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:20:06.614246+00:00
-- url     : https://prove2.me/theorems/82f91167-5026-4ad9-94a7-33984f1da798
-- title:
--   Distance Balancing: classical Word Of Homology Functional mem kernel
-- statement:
--   The Distance Balancing construction uses the classical Word Of Homology Functional mem kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L909-L921
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L909-L921

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

theorem QEC.Coding.DistanceBalancing.classicalWordOfHomologyFunctional_mem_kernel
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (φ : Module.Dual (ZMod 2) (sourceChainComplex D).middleHomology) :
    Matrix.toLin' D.classicalBoundary
      (classicalWordOfHomologyFunctional D z hz φ) = 0 := by sorry
