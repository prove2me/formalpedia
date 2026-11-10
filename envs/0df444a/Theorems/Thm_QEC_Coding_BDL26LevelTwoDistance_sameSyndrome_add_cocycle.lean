-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LevelTwoDistance_sameSyndrome_add_cocycle
-- name    : QEC.Coding.BDL26LevelTwoDistance.sameSyndrome_add_cocycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T01:27:35.813199+00:00
-- url     : https://prove2.me/theorems/da64b21d-b23d-4f60-a92c-a65354f90a4b
-- title:
--   BDL26 Level Two Distance: same Syndrome add cocycle
-- statement:
--   Equal actual syndromes make the error sum a cocycle, before any locality
--   argument is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L82-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LevelTwoDistance.lean#L82-L88

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

theorem QEC.Coding.BDL26LevelTwoDistance.sameSyndrome_add_cocycle (S : OddScale)
    (first second : Word Field (levelTwoPresentation S).Q)
    (h : tannerCoboundary1 (levelTwoPresentation S) first =
      tannerCoboundary1 (levelTwoPresentation S) second) :
    tannerCoboundary1 (levelTwoPresentation S) (first + second) = 0 := by sorry
