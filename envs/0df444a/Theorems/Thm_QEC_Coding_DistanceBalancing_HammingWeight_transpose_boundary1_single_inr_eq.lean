-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_transpose_boundary1_single_inr_eq
-- name    : QEC.Coding.DistanceBalancing.HammingWeight_transpose_boundary1_single_inr_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:26:30.820202+00:00
-- url     : https://prove2.me/theorems/670f81aa-ff6d-4d50-bd55-26d91af53b39
-- title:
--   Distance Balancing: Hamming Weight transpose boundary1 single inr eq
-- statement:
--   The Distance Balancing construction uses the Hamming Weight transpose boundary1 single inr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L121-L144
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L121-L144

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

theorem QEC.Coding.DistanceBalancing.HammingWeight_transpose_boundary1_single_inr_eq
    (x1 : xOne) (b : classicalCheck) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 D)
          (Pi.single (Sum.inr (x1, b)) 1)) =
      HammingWeight (fun a ↦ D.classicalBoundary b a) +
        HammingWeight (fun x2 ↦ D.xBoundary2 x1 x2) := by sorry
