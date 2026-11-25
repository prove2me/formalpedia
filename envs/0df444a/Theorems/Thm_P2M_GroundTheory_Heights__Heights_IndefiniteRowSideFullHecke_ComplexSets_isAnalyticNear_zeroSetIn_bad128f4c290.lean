-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isAnalyticNear_zeroSetIn_bad128f4c290
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isAnalyticNear_zeroSetIn_bad128f4c290
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:38.706357+00:00
-- url     : https://prove2.me/theorems/0abce891-3252-4be1-bc39-95deb70e9c78
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Analytic Near zero Set In bad128f4c290: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Se
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Analytic Near zero Set In bad128f4c290 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets is Analytic Near zero Set In bad128f4c290 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalZerosNowhereDense.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalZerosNowhereDense.lean#L13-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermRegularConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalZerosNowhereDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isAnalyticNear_zeroSetIn_bad128f4c290 {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    IsAnalyticNear (zeroSetIn I) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«isAnalyticNear_zeroSetIn» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isAnalyticNear_zeroSetIn_bad128f4c290
