-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_sourceCochainContraction_add
-- name    : QEC.Coding.DistanceBalancing.sourceCochainContraction_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:12.691679+00:00
-- url     : https://prove2.me/theorems/4992ad27-7614-4fb9-a33a-c8100ed3b651
-- title:
--   Distance Balancing: source Cochain Contraction add
-- statement:
--   The Distance Balancing construction uses the source Cochain Contraction add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L495-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L495-L502

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

theorem QEC.Coding.DistanceBalancing.sourceCochainContraction_add
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (c c' : Word (ZMod 2) classicalBit) :
    sourceCochainContraction x (c + c') =
      sourceCochainContraction x c + sourceCochainContraction x c' := by sorry
