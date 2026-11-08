-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_boundaryColumnWeight_inl_eq
-- name    : QEC.Coding.DistanceBalancing.boundaryColumnWeight_inl_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:26:29.607465+00:00
-- url     : https://prove2.me/theorems/e1e9950f-8578-4ae9-9db0-8305210aac2e
-- title:
--   Distance Balancing: boundary Column Weight inl eq
-- statement:
--   The Distance Balancing construction uses the boundary Column Weight inl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L176-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L176-L224

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

theorem QEC.Coding.DistanceBalancing.boundaryColumnWeight_inl_eq
    (x1 : xOne) (a : classicalBit) :
    HammingWeight (boundary1 D (Pi.single (Sum.inl (x1, a)) 1)) +
        HammingWeight
          (wordLinearMapTranspose (boundary2 D)
            (Pi.single (Sum.inl (x1, a)) 1)) =
      HammingWeight (fun x0 ↦ D.xBoundary1 x0 x1) +
        HammingWeight (fun b ↦ D.classicalBoundary b a) +
        HammingWeight (fun x2 ↦ D.xBoundary2 x1 x2) := by sorry
