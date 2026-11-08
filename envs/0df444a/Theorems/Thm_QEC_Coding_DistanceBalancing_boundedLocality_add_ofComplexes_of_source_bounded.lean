-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_boundedLocality_add_ofComplexes_of_source_bounded
-- name    : QEC.Coding.DistanceBalancing.boundedLocality_add_ofComplexes_of_source_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:27:02.27038+00:00
-- url     : https://prove2.me/theorems/4960a732-1298-40d1-89c1-3b465e91e34a
-- title:
--   Distance Balancing: bounded Locality add of Complexes of source bounded
-- statement:
--   If the source complex already carries a bounded incidence-locality proof,
--   only the classical row and column bounds remain to prove product locality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L466-L501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L466-L501

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

theorem QEC.Coding.DistanceBalancing.boundedLocality_add_ofComplexes_of_source_bounded
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) xZero) (Word (ZMod 2) xOne) (Word (ZMod 2) xTwo))
    (Y : Word (ZMod 2) classicalBit →ₗ[ZMod 2]
      Word (ZMod 2) classicalCheck)
    {sourceBound classicalBound : Nat}
    (hSource : BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile sourceBound)
    (hClassicalRow : ∀ b,
      HammingWeight
        (wordLinearMapTranspose Y (Pi.single b 1)) ≤ classicalBound)
    (hClassicalColumn : ∀ a,
      HammingWeight (Y (Pi.single a 1)) ≤ classicalBound) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (chainComplex (Data.ofComplexes X Y))).localityProfile
      (sourceBound + classicalBound) := by sorry
