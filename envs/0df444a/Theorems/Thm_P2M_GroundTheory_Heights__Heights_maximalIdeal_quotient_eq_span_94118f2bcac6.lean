-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_maximalIdeal_quotient_eq_span_94118f2bcac6
-- name    : P2M_GroundTheory_Heights__Heights_maximalIdeal_quotient_eq_span_94118f2bcac6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:18.752116+00:00
-- url     : https://prove2.me/theorems/ddf91024-a88c-47a7-ad1e-0e4e545dcb7b
-- title:
--   P2 M Ground Theory Heights  Heights maximal Ideal quotient eq span 94118f2bcac6: P2 M Ground Theory Heights  Heights maximal Ideal quotient eq span 94118f2bcac6
-- statement:
--   The P2 M Ground Theory Heights  Heights maximal Ideal quotient eq span 94118f2bcac6 construction uses the P2 M Ground Theory Heights  Heights maximal Ideal quotient eq span 94118f2bcac6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMLengthParameters.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMLengthParameters.lean#L64-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMLengthParameters
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

theorem P2M_GroundTheory_Heights__Heights_maximalIdeal_quotient_eq_span_94118f2bcac6 {B : Type u} [CommRing B] [IsLocalRing B] {I : Ideal B} {k : ℕ}
    (x : Fin k → B) (hI : Ideal.span (Set.range x) ⊔ I = maximalIdeal B) [IsLocalRing (B ⧸ I)] :
    maximalIdeal (B ⧸ I) = Ideal.span (Set.range fun i => Ideal.Quotient.mk I (x i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«maximalIdeal_quotient_eq_span» := P2M_GroundTheory_Heights__Heights_maximalIdeal_quotient_eq_span_94118f2bcac6
