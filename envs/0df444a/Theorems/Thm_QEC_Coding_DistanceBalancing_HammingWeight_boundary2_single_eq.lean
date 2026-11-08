-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_boundary2_single_eq
-- name    : QEC.Coding.DistanceBalancing.HammingWeight_boundary2_single_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:26:53.129842+00:00
-- url     : https://prove2.me/theorems/8b20bbaf-aefa-4a9d-9c0f-b97d79b79229
-- title:
--   Distance Balancing: Hamming Weight boundary2 single eq
-- statement:
--   The Distance Balancing construction uses the Hamming Weight boundary2 single eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L146-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L146-L174

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

theorem QEC.Coding.DistanceBalancing.HammingWeight_boundary2_single_eq
    (x2 : xTwo) (a : classicalBit) :
    HammingWeight (boundary2 D (Pi.single (x2, a) 1)) =
      HammingWeight (fun x1 ↦ D.xBoundary2 x1 x2) +
        HammingWeight (fun b ↦ D.classicalBoundary b a) := by sorry
