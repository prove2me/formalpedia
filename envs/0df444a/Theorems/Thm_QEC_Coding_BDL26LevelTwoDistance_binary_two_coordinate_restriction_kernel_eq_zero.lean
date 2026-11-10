-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_binary_two_coordinate_restriction_kernel_eq_zero
-- name    : QEC.Coding.BDL26LevelTwoDistance.binary_two_coordinate_restriction_kernel_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:48:53.264544+00:00
-- url     : https://prove2.me/theorems/f939ed3d-e825-4108-966d-441be71126de
-- title:
--   BDL26 Level Two Distance: binary two coordinate restriction kernel eq zero
-- statement:
--   Restricting a two-coordinate-supported word along an injective coordinate
--   embedding preserves the elementary two-column separation criterion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1035-L1059
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1035-L1059

import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXSeedSmallSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoCode
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AlternatingCochain
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26LevelTwoDistance
open scoped BigOperators
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementCochainMaps BDL26LevelTwoCode
attribute [local instance] QEC.Coding.BDL26LevelTwoDistance.rzQDecidableEq
open BDL26DecodingGraph

theorem QEC.Coding.BDL26LevelTwoDistance.binary_two_coordinate_restriction_kernel_eq_zero
    {Q I Z : Type} [Fintype Q] [DecidableEq Q] [Fintype I] [DecidableEq I]
    [Fintype Z] [DecidableEq Z]
    (embed : I → Q) (hinj : Function.Injective embed)
    (syndrome : Word Field I →ₗ[Field] Word Field Z)
    (hnonzero : ∀ i, syndrome (canonicalBasisWord i) ≠ 0)
    (hdistinct : Function.Injective (fun i => syndrome (canonicalBasisWord i)))
    (word : Word Field Q)
    (hzero : syndrome (fun i => word (embed i)) = 0) (a b : Q)
    (hsupport : ∀ q, word q ≠ 0 → q = a ∨ q = b) :
    (fun i => word (embed i)) = 0 := by sorry
