-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveNormalisationLength_proof_765dbfa8dadd
-- name    : P2M_GroundTheory_Heights__Heights_CurveNormalisationLength_proof_765dbfa8dadd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:15:38.426354+00:00
-- url     : https://prove2.me/theorems/3b3f303b-c42e-49e9-9f5a-e8fa804aa43a
-- title:
--   P2 M Ground Theory Heights  Heights Curve Normalisation Length proof 765dbfa8dadd: P2 M Ground Theory Heights  Heights Curve Normalisation Length proof 765dbfa8dadd
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Normalisation Length proof 765dbfa8dadd construction uses the P2 M Ground Theory Heights  Heights Curve Normalisation Length proof 765dbfa8dadd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveNormalisationLength.lean#L64-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveNormalisationLength.lean#L64-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StExtensionQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PLengthDecomp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveNormalisationLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_LengthDecomp_proof_ad84518a0f0a

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

theorem P2M_GroundTheory_Heights__Heights_CurveNormalisationLength_proof_765dbfa8dadd (hFin : CurveNormalisationFinite.Statement)
    (hQ : CurveNormalisationQuotientLength.Statement) (hE : ExtensionQuotientLength.Statement) :
    CurveNormalisationLength.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveNormalisationLength».«proof» := P2M_GroundTheory_Heights__Heights_CurveNormalisationLength_proof_765dbfa8dadd
