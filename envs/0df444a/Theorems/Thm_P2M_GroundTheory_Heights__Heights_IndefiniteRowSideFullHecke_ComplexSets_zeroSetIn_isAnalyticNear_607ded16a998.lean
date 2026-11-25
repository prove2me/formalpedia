-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroSetIn_isAnalyticNear_607ded16a998
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroSetIn_isAnalyticNear_607ded16a998
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:23:15.111486+00:00
-- url     : https://prove2.me/theorems/7ba312c1-ae80-5bcf-aec8-beb842a0bdfd
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets zero Set In is Analytic Near 607ded16a998: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Se
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets zero Set In is Analytic Near 607ded16a998 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets zero Set In is Analytic Near 607ded16a998 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalComplementConnected.lean#L13-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalComplementConnected.lean#L13-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVanishNearPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalComplementConnected
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroSetIn_isAnalyticNear_607ded16a998 {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    IsAnalyticNear (zeroSetIn I) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«zeroSetIn_isAnalyticNear» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_zeroSetIn_isAnalyticNear_607ded16a998
