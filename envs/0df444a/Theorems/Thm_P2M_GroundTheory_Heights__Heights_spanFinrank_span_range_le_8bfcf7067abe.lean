-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_spanFinrank_span_range_le_8bfcf7067abe
-- name    : P2M_GroundTheory_Heights__Heights_spanFinrank_span_range_le_8bfcf7067abe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:01.943012+00:00
-- url     : https://prove2.me/theorems/9ad7f3c3-6277-4d22-a66e-af5c77823372
-- title:
--   P2 M Ground Theory Heights  Heights span Finrank span range le 8bfcf7067abe: P2 M Ground Theory Heights  Heights span Finrank span range le 8bfcf7067abe
-- statement:
--   The P2 M Ground Theory Heights  Heights span Finrank span range le 8bfcf7067abe construction uses the P2 M Ground Theory Heights  Heights span Finrank span range le 8bfcf7067abe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMLengthParameters.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCMLengthParameters.lean#L46-L52

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

theorem P2M_GroundTheory_Heights__Heights_spanFinrank_span_range_le_8bfcf7067abe {R : Type*} [CommRing R] {k : ℕ} (z : Fin k → R) :
    (Ideal.span (Set.range z)).spanFinrank ≤ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«spanFinrank_span_range_le» := P2M_GroundTheory_Heights__Heights_spanFinrank_span_range_le_8bfcf7067abe
