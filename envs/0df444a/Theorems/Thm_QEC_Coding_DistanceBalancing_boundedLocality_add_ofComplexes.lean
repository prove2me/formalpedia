-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_boundedLocality_add_ofComplexes
-- name    : QEC.Coding.DistanceBalancing.boundedLocality_add_ofComplexes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:26:43.836133+00:00
-- url     : https://prove2.me/theorems/c74e3287-186e-4b51-9009-e443411fbf50
-- title:
--   Distance Balancing: bounded Locality add of Complexes
-- statement:
--   Map-level version of `boundedLocality_add` for the construction-owned
--   `Data.ofComplexes` entry point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L340-L405
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L340-L405

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

theorem QEC.Coding.DistanceBalancing.boundedLocality_add_ofComplexes
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      Word (ZMod 2) classicalCheck)
    {sourceBound classicalBound : Nat}
    (hSourceX : ∀ x0,
      HammingWeight
        (wordLinearMapTranspose X.boundary1
          (canonicalBasisWord (F := ZMod 2) x0)) ≤ sourceBound)
    (hSourceZ : ∀ x2,
      HammingWeight
        (X.boundary2 (canonicalBasisWord (F := ZMod 2) x2)) ≤ sourceBound)
    (hSourceVariable : ∀ x1,
      HammingWeight
          (X.boundary1 (canonicalBasisWord (F := ZMod 2) x1)) +
        HammingWeight
          (wordLinearMapTranspose X.boundary2
            (canonicalBasisWord (F := ZMod 2) x1)) ≤ sourceBound)
    (hClassicalRow : ∀ b,
      HammingWeight
        (wordLinearMapTranspose Y (Pi.single b 1)) ≤ classicalBound)
    (hClassicalColumn : ∀ a,
      HammingWeight (Y (Pi.single a 1)) ≤ classicalBound) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (chainComplex (Data.ofComplexes X Y))).localityProfile
      (sourceBound + classicalBound) := by sorry
