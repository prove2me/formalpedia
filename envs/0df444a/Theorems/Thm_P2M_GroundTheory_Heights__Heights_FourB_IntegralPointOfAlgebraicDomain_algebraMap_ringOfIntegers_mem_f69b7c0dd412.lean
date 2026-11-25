-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_algebraMap_ringOfIntegers_mem_f69b7c0dd412
-- name    : P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_algebraMap_ringOfIntegers_mem_f69b7c0dd412
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:56:19.422419+00:00
-- url     : https://prove2.me/theorems/e9a41af8-784c-40d5-ab85-0e645c2e9322
-- title:
--   P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain algebra Map ring Of Integers mem f69b7c0dd412: P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Doma
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain algebra Map ring Of Integers mem f69b7c0dd412 construction uses the P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain algebra Map ring Of Integers mem f69b7c0dd412 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointOfAlgebraicDomain.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointOfAlgebraicDomain.lean#L76-L81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPointAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralPointOfAlgebraicDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain
variable {K : Type*} [Field K] {S : Type*} [CommRing S]
  [Algebra S K] [IsFractionRing S K] (M : Ideal S) [M.IsMaximal]

theorem P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_algebraMap_ringOfIntegers_mem_f69b7c0dd412 [NumberField K] (B : ValuationSubring K) (x : 𝓞 K) :
    algebraMap (𝓞 K) K x ∈ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«IntegralPointOfAlgebraicDomain».«algebraMap_ringOfIntegers_mem» := P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_algebraMap_ringOfIntegers_mem_f69b7c0dd412
