-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_span_eq_of_isRegularLocalRing_quotient_90ce8f3deba0
-- name    : P2M_GroundTheory_Heights__Heights_exists_span_eq_of_isRegularLocalRing_quotient_90ce8f3deba0
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:11.061128+00:00
-- url     : https://prove2.me/theorems/b17e15c0-feeb-47dc-9143-7f48c259e595
-- title:
--   P2 M Ground Theory Heights  Heights exists span eq of is Regular Local Ring quotient 90ce8f3deba0: P2 M Ground Theory Heights  Heights exists span eq of is Regular Local Ring quotient 90ce8f3deba0
-- statement:
--   The P2 M Ground Theory Heights  Heights exists span eq of is Regular Local Ring quotient 90ce8f3deba0 construction uses the P2 M Ground Theory Heights  Heights exists span eq of is Regular Local Ring quotient 90ce8f3deba0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RegularQuotientGenerators.lean#L50-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RegularQuotientGenerators.lean#L50-L129

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RegularQuotientGenerators
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
open IsLocalRing Ideal
universe u

theorem P2M_GroundTheory_Heights__Heights_exists_span_eq_of_isRegularLocalRing_quotient_90ce8f3deba0 (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (I : Ideal R) [IsRegularLocalRing (R ⧸ I)],
      ringKrullDim R = ringKrullDim (R ⧸ I) + n →
        ∃ f : Fin n → R, (∀ j, f j ∈ I) ∧ I = Ideal.span (Set.range f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_span_eq_of_isRegularLocalRing_quotient» := P2M_GroundTheory_Heights__Heights_exists_span_eq_of_isRegularLocalRing_quotient_90ce8f3deba0
