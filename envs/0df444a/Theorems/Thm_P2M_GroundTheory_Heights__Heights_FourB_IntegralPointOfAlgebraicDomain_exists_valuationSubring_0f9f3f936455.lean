-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_exists_valuationSubring_0f9f3f936455
-- name    : P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_exists_valuationSubring_0f9f3f936455
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:50:08.600476+00:00
-- url     : https://prove2.me/theorems/b26f93e3-0ba6-521d-ae1b-03ebe191fec2
-- title:
--   P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain exists valuation Subring 0f9f3f936455: P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain exist
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain exists valuation Subring 0f9f3f936455 construction uses the P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain exists valuation Subring 0f9f3f936455 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointOfAlgebraicDomain.lean#L59-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointOfAlgebraicDomain.lean#L59-L74

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

theorem P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_exists_valuationSubring_0f9f3f936455 :
    ∃ B : ValuationSubring K, (∀ s : S, algebraMap S K s ∈ B) ∧
      ∀ s ∈ M, B.valuation (algebraMap S K s) < 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«IntegralPointOfAlgebraicDomain».«exists_valuationSubring» := P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_exists_valuationSubring_0f9f3f936455
