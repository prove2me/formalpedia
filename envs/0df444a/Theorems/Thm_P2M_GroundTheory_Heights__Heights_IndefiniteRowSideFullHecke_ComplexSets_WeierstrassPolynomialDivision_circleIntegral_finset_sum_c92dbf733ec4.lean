-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_circleIntegral_finset_sum_c92dbf733ec4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_circleIntegral_finset_sum_c92dbf733ec4
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:20:05.148048+00:00
-- url     : https://prove2.me/theorems/71e4d5eb-e01f-5b5a-8232-6efa5fcc5a2a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Weierstrass Polynomial Division circle Integral finset sum c92dbf733ec4: P2 M Ground Theory Heights  Heights Indefinite
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Weierstrass Polynomial Division circle Integral finset sum c92dbf733ec4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Weierstrass Polynomial Division circle Integral finset sum c92dbf733ec4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeierstrassPolynomialDivision.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeierstrassPolynomialDivision.lean#L15-L25

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_circleIntegral_finset_sum_c92dbf733ec4 {ι : Type} (u : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ i ∈ u, ContinuousOn (f i) (sphere c R)) :
    (∮ z in C(c, R), ∑ i ∈ u, f i z) = ∑ i ∈ u, ∮ z in C(c, R), f i z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«WeierstrassPolynomialDivision».«circleIntegral_finset_sum» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_circleIntegral_finset_sum_c92dbf733ec4
