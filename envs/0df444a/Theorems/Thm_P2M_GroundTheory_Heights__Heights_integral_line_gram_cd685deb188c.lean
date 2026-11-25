-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_integral_line_gram_cd685deb188c
-- name    : P2M_GroundTheory_Heights__Heights_integral_line_gram_cd685deb188c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:15.560416+00:00
-- url     : https://prove2.me/theorems/e7ccec71-d8a6-4ee6-bac8-edd95ec6a867
-- title:
--   P2 M Ground Theory Heights  Heights integral line gram cd685deb188c: P2 M Ground Theory Heights  Heights integral line gram cd685deb188c
-- statement:
--   The P2 M Ground Theory Heights  Heights integral line gram cd685deb188c construction uses the P2 M Ground Theory Heights  Heights integral line gram cd685deb188c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeChartGram.lean#L69-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeChartGram.lean#L69-L118

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeChartGram
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
open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_integral_line_gram_cd685deb188c {n : ℕ} (e : ℕ) (h : HermNorm n) (g : (Fin n → ℂ) → ℝ)
    (hg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) (x : Fin n → ℂ) (hx : x ≠ 0) (G : ℝ) :
    ∫ t : ℂ, (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => g (h.pointOf z))
          (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G) =
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        (g x * ((e.factorial : ℝ) / Real.pi ^ e * G / h.dualNorm x ^ (2 * (e + 1)))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«integral_line_gram» := P2M_GroundTheory_Heights__Heights_integral_line_gram_cd685deb188c
