-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_sourceCochainContraction_single
-- name    : QEC.Coding.DistanceBalancing.sourceCochainContraction_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:19:21.001216+00:00
-- url     : https://prove2.me/theorems/eaf8d1a5-b2bd-4dab-8648-77847dd2a318
-- title:
--   Distance Balancing: source Cochain Contraction single
-- statement:
--   The Distance Balancing construction uses the source Cochain Contraction single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L504-L516
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Core.lean#L504-L516

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

theorem QEC.Coding.DistanceBalancing.sourceCochainContraction_single
    (x : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (a : classicalBit) :
    sourceCochainContraction x (Pi.single a 1) = xOneBitSlice x a := by sorry
