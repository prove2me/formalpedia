-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_transpose_sourceBoundary1_projectedSourceCochainFilling
-- name    : QEC.Coding.DistanceBalancing.transpose_sourceBoundary1_projectedSourceCochainFilling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:50.594415+00:00
-- url     : https://prove2.me/theorems/c4de4a05-1e1c-4b13-976b-49b63a895531
-- title:
--   Distance Balancing: transpose source Boundary1 projected Source Cochain Filling
-- statement:
--   The Distance Balancing construction uses the transpose source Boundary1 projected Source Cochain Filling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L665-L678
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L665-L678

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

theorem QEC.Coding.DistanceBalancing.transpose_sourceBoundary1_projectedSourceCochainFilling
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hFill : ∀ a : classicalBit,
      projectedSourceCochain D S x a ∈
        (sourceChainComplex D).firstCoboundaryCheckCode.carrier)
    (a : classicalBit) :
    wordLinearMapTranspose (sourceChainComplex D).boundary1
      (projectedSourceCochainFilling D S x hFill a) =
        projectedSourceCochain D S x a := by sorry
