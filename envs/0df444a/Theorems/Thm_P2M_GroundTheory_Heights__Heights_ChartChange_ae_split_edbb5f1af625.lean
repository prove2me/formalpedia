-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartChange_ae_split_edbb5f1af625
-- name    : P2M_GroundTheory_Heights__Heights_ChartChange_ae_split_edbb5f1af625
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:17:57.505333+00:00
-- url     : https://prove2.me/theorems/956d7821-e554-47dc-940b-dc5d4bb9889b
-- title:
--   P2 M Ground Theory Heights  Heights Chart Change ae split edbb5f1af625: P2 M Ground Theory Heights  Heights Chart Change ae split edbb5f1af625
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Change ae split edbb5f1af625 construction uses the P2 M Ground Theory Heights  Heights Chart Change ae split edbb5f1af625 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntChartChange.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntChartChange.lean#L46-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntChartChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPosPartSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIntegralIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntChartChange
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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.ChartChange
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartChange_ae_split_edbb5f1af625 {K : Ideal (MvPolynomial (Fin n) ℂ)} {B : Matrix (Fin d) (Fin n) ℂ}
    (w : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) (F : ℕ → Set (Fin n → ℂ))
    (P : (Fin n → ℂ) → Prop) (hB : IsFiniteProjection K B) (hF : Pairwise (Function.onFun Disjoint F))
    (h0 : volume ((fun x => B *ᵥ x) '' {x | x ∈ zeroSet K ∧ (∃ s, IsSheetAt K B x s) ∧ ¬ P x}) = 0)
    (hc : ∀ x ∈ zeroSet K, (∃ s, IsSheetAt K B x s) → P x → ∃ k, x ∈ F k) :
    ∀ᵐ y, ENNReal.ofReal (chartPosDens K B w ψ y) =
      ∑' k, ENNReal.ofReal (chartPosDens K B ((F k).indicator w) ψ y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartChange».«ae_split» := P2M_GroundTheory_Heights__Heights_ChartChange_ae_split_edbb5f1af625
