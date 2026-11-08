-- Prove2me | Theorems.Thm_QEC_Coding_DistanceBalancing_boundedLocality_of_canonical_boundary_bounds
-- name    : QEC.Coding.DistanceBalancing.boundedLocality_of_canonical_boundary_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:42:48.933215+00:00
-- url     : https://prove2.me/theorems/f230dfa0-7bbb-4790-a27c-168d01741391
-- title:
--   Distance Balancing: bounded Locality of canonical boundary bounds
-- statement:
--   Canonical-basis version of the chain-complex locality constructor.  This
--   keeps the chosen `DecidableEq` implementation out of downstream theorem
--   interfaces, which is important for large construction-owned index types.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L53-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/CodeReduction/DistanceBalancing/Locality.lean#L53-L79

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

theorem QEC.Coding.DistanceBalancing.boundedLocality_of_canonical_boundary_bounds
    {zero one two : Type u}
    [Fintype zero] [DecidableEq zero]
    [Fintype one] [DecidableEq one]
    [Fintype two] [DecidableEq two]
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) zero) (Word (ZMod 2) one) (Word (ZMod 2) two))
    {checkBound variableBound : Nat}
    (hZero : ∀ x0,
      HammingWeight
        (wordLinearMapTranspose X.boundary1
          (canonicalBasisWord (F := ZMod 2) x0)) ≤ checkBound)
    (hTwo : ∀ x2,
      HammingWeight
        (X.boundary2 (canonicalBasisWord (F := ZMod 2) x2)) ≤ checkBound)
    (hVariable : ∀ x1,
      ((QEC.QLDPC.chainComplexBoundaryIncidence X).variableSupport x1).card ≤
        variableBound) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile
      (max checkBound variableBound) := by sorry
