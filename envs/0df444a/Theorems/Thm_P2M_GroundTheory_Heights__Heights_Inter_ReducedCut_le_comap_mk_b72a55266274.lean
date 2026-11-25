-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_le_comap_mk_b72a55266274
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_le_comap_mk_b72a55266274
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:15.624539+00:00
-- url     : https://prove2.me/theorems/5318783c-f609-45ec-b1d6-603f82d283a1
-- title:
--   P2 M Ground Theory Heights  Heights Inter Reduced Cut le comap mk b72a55266274: P2 M Ground Theory Heights  Heights Inter Reduced Cut le comap mk b72a55266274
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Reduced Cut le comap mk b72a55266274 construction uses the P2 M Ground Theory Heights  Heights Inter Reduced Cut le comap mk b72a55266274 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PReducedCutLength.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PReducedCutLength.lean#L65-L68

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
variable {T : Type} [CommRing T] (I : Ideal T) (x : T) (Q : Ideal T) [Q.IsPrime]
local notation "𝓛" => Localization.AtPrime Q
local notation "ι" => algebraMap T (Localization.AtPrime Q)
local notation "𝓘" => Ideal.map (algebraMap T (Localization.AtPrime Q)) I
local notation "𝓐" => Localization.AtPrime Q ⧸ Ideal.map (algebraMap T (Localization.AtPrime Q)) I
local notation "π" => Ideal.Quotient.mk (Ideal.map (algebraMap T (Localization.AtPrime Q)) I)

theorem P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_le_comap_mk_b72a55266274 (p : Ideal 𝓐) : 𝓘 ≤ p.comap π := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ReducedCut».«le_comap_mk» := P2M_GroundTheory_Heights__Heights_Inter_ReducedCut_le_comap_mk_b72a55266274
