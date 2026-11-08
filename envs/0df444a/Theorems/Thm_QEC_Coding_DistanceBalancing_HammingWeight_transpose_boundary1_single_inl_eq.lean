-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_HammingWeight_transpose_boundary1_single_inl_eq
-- name    : QEC.Coding.DistanceBalancing.HammingWeight_transpose_boundary1_single_inl_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:26:00.838633+00:00
-- url     : https://prove2.me/theorems/020daf3b-001d-4b19-96bb-24bd27a174bc
-- title:
--   Distance Balancing: Hamming Weight transpose boundary1 single inl eq
-- statement:
--   The Distance Balancing construction uses the Hamming Weight transpose boundary1 single inl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L96-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L96-L119

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

theorem QEC.Coding.DistanceBalancing.HammingWeight_transpose_boundary1_single_inl_eq
    (x0 : xZero) (a : classicalBit) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 D)
          (Pi.single (Sum.inl (x0, a)) 1)) =
      HammingWeight (fun x1 ↦ D.xBoundary1 x0 x1) := by sorry
