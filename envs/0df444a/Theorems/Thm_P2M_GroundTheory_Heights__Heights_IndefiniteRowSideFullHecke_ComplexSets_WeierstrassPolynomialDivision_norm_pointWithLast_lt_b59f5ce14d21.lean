-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_norm_pointWithLast_lt_b59f5ce14d21
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_norm_pointWithLast_lt_b59f5ce14d21
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:02.143878+00:00
-- url     : https://prove2.me/theorems/d7b229ae-78d7-4029-90a7-7db971872e3a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Weierstrass Polynomial Division norm point With Last lt b59f5ce14d21: P2 M Ground Theory Heights  Heights Indefinite Row
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Weierstrass Polynomial Division norm point With Last lt b59f5ce14d21 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Weierstrass Polynomial Division norm point With Last lt b59f5ce14d21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeierstrassPolynomialDivision.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeierstrassPolynomialDivision.lean#L41-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassPolynomialDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonicDifferenceQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeierstrassPolynomialDivision
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
open Topology Filter Metric Complex Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.WeierstrassPolynomialDivision

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_norm_pointWithLast_lt_b59f5ce14d21 {σ : Type} [Fintype σ] {z : σ → ℂ} {s : ℂ} {ε : ℝ} (hε : 0 < ε) (hz : ‖z‖ < ε)
    (hs : ‖s‖ < ε) : ‖pointWithLast z s‖ < ε := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«WeierstrassPolynomialDivision».«norm_pointWithLast_lt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_norm_pointWithLast_lt_b59f5ce14d21
