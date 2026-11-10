-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_binary_two_coordinate_matrix_restriction_eq_zero
-- name    : QEC.Coding.BDL26LevelTwoDistance.binary_two_coordinate_matrix_restriction_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:38:37.514325+00:00
-- url     : https://prove2.me/theorems/2a497a4a-4711-4ea9-a75e-e5ea8a6f1652
-- title:
--   BDL26 Level Two Distance: binary two coordinate matrix restriction eq zero
-- statement:
--   A matrix with nonzero distinct rows has no binary kernel vector on two
--   source coordinates under its transpose incidence map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1171-L1192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L1171-L1192

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

theorem QEC.Coding.BDL26LevelTwoDistance.binary_two_coordinate_matrix_restriction_eq_zero
    {Q I Z : Type} [Fintype Q] [DecidableEq Q] [Fintype I] [DecidableEq I]
    [Fintype Z] [DecidableEq Z]
    (embed : I → Q) (hinj : Function.Injective embed) (matrix : Matrix I Z Field)
    (hnonzero : ∀ i, ∃ z, matrix i z = 1)
    (hdistinct : Function.Injective (fun i => fun z => matrix i z))
    (word : Word Field Q)
    (hzero : wordLinearMapTranspose (Matrix.toLin' matrix) (fun i => word (embed i)) = 0)
    (a b : Q) (hsupport : ∀ q, word q ≠ 0 → q = a ∨ q = b) :
    (fun i => word (embed i)) = 0 := by sorry
