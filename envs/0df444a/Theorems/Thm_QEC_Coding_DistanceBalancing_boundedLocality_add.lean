-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_boundedLocality_add
-- name    : QEC.Coding.DistanceBalancing.boundedLocality_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:26:22.02588+00:00
-- url     : https://prove2.me/theorems/3786122f-327b-4c83-a430-0155372ad0dd
-- title:
--   Distance Balancing: bounded Locality add
-- statement:
--   Locality bounds for both input factors add under the finite EKZ product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L279-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L279-L336

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

theorem QEC.Coding.DistanceBalancing.boundedLocality_add
    {sourceBound classicalBound : Nat}
    (hSourceX : ∀ x0,
      HammingWeight (fun x1 ↦ D.xBoundary1 x0 x1) ≤ sourceBound)
    (hSourceZ : ∀ x2,
      HammingWeight (fun x1 ↦ D.xBoundary2 x1 x2) ≤ sourceBound)
    (hSourceVariable : ∀ x1,
      HammingWeight (fun x0 ↦ D.xBoundary1 x0 x1) +
        HammingWeight (fun x2 ↦ D.xBoundary2 x1 x2) ≤ sourceBound)
    (hClassicalRow : ∀ b,
      HammingWeight (fun a ↦ D.classicalBoundary b a) ≤ classicalBound)
    (hClassicalColumn : ∀ a,
      HammingWeight (fun b ↦ D.classicalBoundary b a) ≤ classicalBound) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (chainComplex D)).localityProfile
      (sourceBound + classicalBound) := by sorry
