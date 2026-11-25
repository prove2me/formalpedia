-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_scalar_fin_983e343b1d19
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_scalar_fin_983e343b1d19
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:34.38284+00:00
-- url     : https://prove2.me/theorems/444d39ad-6177-4d97-a735-0f689382a7de
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic On Nhd of differentiable On scalar fin 983e343b1d19: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic On Nhd of differentiable On scalar fin 983e343b1d19 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic On Nhd of differentiable On scalar fin 983e343b1d19 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalZerosNowhereDense.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalZerosNowhereDense.lean#L34-L40

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_scalar_fin_983e343b1d19 {d : ℕ} {U : Set (Fin d → ℂ)} {F : (Fin d → ℂ) → ℂ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) : AnalyticOnNhd ℂ F U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«analyticOnNhd_of_differentiableOn_scalar_fin» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticOnNhd_of_differentiableOn_scalar_fin_983e343b1d19
