-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_localMult_map_of_flat_9840763cb348
-- name    : P2M_GroundTheory_Heights__Heights_localMult_map_of_flat_9840763cb348
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:38.976532+00:00
-- url     : https://prove2.me/theorems/7eb2308a-d443-4947-8537-d11d59a40273
-- title:
--   P2 M Ground Theory Heights  Heights local Mult map of flat 9840763cb348: P2 M Ground Theory Heights  Heights local Mult map of flat 9840763cb348
-- statement:
--   The P2 M Ground Theory Heights  Heights local Mult map of flat 9840763cb348 construction uses the P2 M Ground Theory Heights  Heights local Mult map of flat 9840763cb348 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFundCycleBaseChange.lean#L12-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PFundCycleBaseChange.lean#L12-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsFundCycleBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMinimalPrimeComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PRadicalBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFundCycleBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_localMult_map_of_flat_9840763cb348 {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (J W : Ideal A) [W.IsPrime] (W' : Ideal B) [W'.IsPrime] [W'.LiesOver W]
    (hfib : (W.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime W')) =
      IsLocalRing.maximalIdeal (Localization.AtPrime W')) :
    localMult (J.map (algebraMap A B)) W' = localMult J W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«localMult_map_of_flat» := P2M_GroundTheory_Heights__Heights_localMult_map_of_flat_9840763cb348
