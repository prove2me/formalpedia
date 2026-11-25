-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_quotient_sup_span_df8b16fd9334
-- name    : P2M_GroundTheory_Heights__Heights_length_quotient_sup_span_df8b16fd9334
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:48:00.25647+00:00
-- url     : https://prove2.me/theorems/0bf6c466-ad23-49db-8db0-c149b19701e4
-- title:
--   P2 M Ground Theory Heights  Heights length quotient sup span df8b16fd9334: P2 M Ground Theory Heights  Heights length quotient sup span df8b16fd9334
-- statement:
--   The P2 M Ground Theory Heights  Heights length quotient sup span df8b16fd9334 construction uses the P2 M Ground Theory Heights  Heights length quotient sup span df8b16fd9334 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveNormalisationLength.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveNormalisationLength.lean#L17-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StExtensionQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveNormalisationLength
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
open MvPolynomial ComplexSets
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_length_quotient_sup_span_df8b16fd9334 {L : Type} [CommRing L] (J : Ideal L) (g : L) :
    Module.length L (L ⧸ (J ⊔ Ideal.span {g})) =
      Module.length (L ⧸ J) ((L ⧸ J) ⧸ Ideal.span {Ideal.Quotient.mk J g}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«length_quotient_sup_span» := P2M_GroundTheory_Heights__Heights_length_quotient_sup_span_df8b16fd9334
