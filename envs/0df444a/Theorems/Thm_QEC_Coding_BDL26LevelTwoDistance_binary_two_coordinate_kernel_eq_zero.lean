-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_binary_two_coordinate_kernel_eq_zero
-- name    : QEC.Coding.BDL26LevelTwoDistance.binary_two_coordinate_kernel_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:48:41.949377+00:00
-- url     : https://prove2.me/theorems/087a9eed-78eb-4dbb-9860-e2a888a50596
-- title:
--   BDL26 Level Two Distance: binary two coordinate kernel eq zero
-- statement:
--   Nonzero distinct binary syndrome columns separate all words supported on
--   at most two coordinates. This elementary incidence criterion has no distance
--   or radius hypothesis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L934-L985
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L934-L985

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

theorem QEC.Coding.BDL26LevelTwoDistance.binary_two_coordinate_kernel_eq_zero
    {Q Z : Type} [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
    (syndrome : Word Field Q →ₗ[Field] Word Field Z)
    (hnonzero : ∀ q, syndrome (canonicalBasisWord q) ≠ 0)
    (hdistinct : Function.Injective (fun q => syndrome (canonicalBasisWord q)))
    (word : Word Field Q) (hzero : syndrome word = 0) (a b : Q)
    (hsupport : ∀ q, word q ≠ 0 → q = a ∨ q = b) : word = 0 := by sorry
