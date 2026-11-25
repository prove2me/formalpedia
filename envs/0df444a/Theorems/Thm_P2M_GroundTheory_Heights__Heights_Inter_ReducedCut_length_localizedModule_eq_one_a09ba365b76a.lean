-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_length_localizedModule_eq_one_a09ba365b76a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_length_localizedModule_eq_one_a09ba365b76a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:45.270193+00:00
-- url     : https://prove2.me/theorems/fcf384b4-b1d5-4714-9a0c-a1b8bd7477c7
-- title:
--   P2 M Ground Theory Heights  Heights Inter Reduced Cut length localized Module eq one a09ba365b76a: P2 M Ground Theory Heights  Heights Inter Reduced Cut length localized Module eq one a09ba365b76a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Reduced Cut length localized Module eq one a09ba365b76a construction uses the P2 M Ground Theory Heights  Heights Inter Reduced Cut length localized Module eq one a09ba365b76a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PReducedCutLength.lean#L21-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PReducedCutLength.lean#L21-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsReducedCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OrdModEqLengthQuotSup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PReducedCutLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Inter.ReducedCut
open IsLocalRing

theorem P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_length_localizedModule_eq_one_a09ba365b76a {B : Type*} [CommRing B] (hB : (⊥ : Ideal B).IsRadical)
    (p : Ideal B) [p.IsPrime] (hp : p ∈ (⊥ : Ideal B).minimalPrimes) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl B) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ReducedCut».«length_localizedModule_eq_one» := P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_length_localizedModule_eq_one_a09ba365b76a
