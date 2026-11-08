-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_boundaryColumnWeight_inr_eq
-- name    : QEC.Coding.DistanceBalancing.boundaryColumnWeight_inr_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:26:33.856607+00:00
-- url     : https://prove2.me/theorems/83f6956a-cf6d-4488-8e33-4316e8c78ada
-- title:
--   Distance Balancing: boundary Column Weight inr eq
-- statement:
--   The Distance Balancing construction uses the boundary Column Weight inr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L226-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L226-L264

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

theorem QEC.Coding.DistanceBalancing.boundaryColumnWeight_inr_eq
    (x2 : xTwo) (b : classicalCheck) :
    HammingWeight (boundary1 D (Pi.single (Sum.inr (x2, b)) 1)) +
        HammingWeight
          (wordLinearMapTranspose (boundary2 D)
            (Pi.single (Sum.inr (x2, b)) 1)) =
      HammingWeight (fun x1 ↦ D.xBoundary2 x1 x2) +
        HammingWeight (fun a ↦ D.classicalBoundary b a) := by sorry
