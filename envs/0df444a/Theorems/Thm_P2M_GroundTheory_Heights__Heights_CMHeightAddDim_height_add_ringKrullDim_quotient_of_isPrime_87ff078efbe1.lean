-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CMHeightAddDim_height_add_ringKrullDim_quotient_of_isPrime_87ff078efbe1
-- name    : P2M_GroundTheory_Heights__Heights_CMHeightAddDim_height_add_ringKrullDim_quotient_of_isPrime_87ff078efbe1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:38.902207+00:00
-- url     : https://prove2.me/theorems/cbae9b62-e668-42f0-add6-2be2a08bbed5
-- title:
--   P2 M Ground Theory Heights  Heights CMHeight Add Dim height add ring Krull Dim quotient of is Prime 87ff078efbe1: P2 M Ground Theory Heights  Heights CMHeight Add Dim height add ring Krull Dim quotien
-- statement:
--   The P2 M Ground Theory Heights  Heights CMHeight Add Dim height add ring Krull Dim quotient of is Prime 87ff078efbe1 construction uses the P2 M Ground Theory Heights  Heights CMHeight Add Dim height add ring Krull Dim quotient of is Prime 87ff078efbe1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMHeightAddDim.lean#L14-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMHeightAddDim.lean#L14-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CMDepthAssoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HeightCoheightQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMHeightAddDim
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
open IsLocalRing
universe u

theorem P2M_GroundTheory_Heights__Heights_CMHeightAddDim_height_add_ringKrullDim_quotient_of_isPrime_87ff078efbe1 (hreg : CMRegularElement.Statement.{u}) :
    ∀ (n : ℕ) (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B], ringKrullDim B = n →
      ∀ (P : Ideal B) [P.IsPrime], (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) = ringKrullDim B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CMHeightAddDim».«height_add_ringKrullDim_quotient_of_isPrime» := P2M_GroundTheory_Heights__Heights_CMHeightAddDim_height_add_ringKrullDim_quotient_of_isPrime_87ff078efbe1
