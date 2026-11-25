-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_pointWithLast_eta_aa55d5e51d8b
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_pointWithLast_eta_aa55d5e51d8b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:35.458301+00:00
-- url     : https://prove2.me/theorems/85b959f9-5a3d-4ae0-a5b2-fe6dcffc2442
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Weierstrass Polynomial Division point With Last eta aa55d5e51d8b: P2 M Ground Theory Heights  Heights Indefinite Row Sid
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Weierstrass Polynomial Division point With Last eta aa55d5e51d8b construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Weierstrass Polynomial Division point With Last eta aa55d5e51d8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeierstrassPolynomialDivision.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeierstrassPolynomialDivision.lean#L27-L29

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_pointWithLast_eta_aa55d5e51d8b {σ : Type} (x : Option σ → ℂ) : pointWithLast (fun i => x (some i)) (x none) = x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«WeierstrassPolynomialDivision».«pointWithLast_eta» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_pointWithLast_eta_aa55d5e51d8b
