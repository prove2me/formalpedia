-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_lintegral_pi_prod_752dfe38d72d
-- name    : P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_lintegral_pi_prod_752dfe38d72d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:12.908167+00:00
-- url     : https://prove2.me/theorems/591b0eea-11cb-4888-9a2c-4f820e112a4b
-- title:
--   P2 M Ground Theory Heights  Heights Lead Block Gauss Tail lintegral pi prod 752dfe38d72d: P2 M Ground Theory Heights  Heights Lead Block Gauss Tail lintegral pi prod 752dfe38d72d
-- statement:
--   The P2 M Ground Theory Heights  Heights Lead Block Gauss Tail lintegral pi prod 752dfe38d72d construction uses the P2 M Ground Theory Heights  Heights Lead Block Gauss Tail lintegral pi prod 752dfe38d72d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L15-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L15-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
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
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail

theorem P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_lintegral_pi_prod_752dfe38d72d {E : Type*} [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] :
    ∀ (n : ℕ) (f : Fin n → E → ℝ≥0∞), (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi (fun _ => μ) = ∏ i, ∫⁻ y, f i y ∂μ
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LeadBlockGaussTail».«lintegral_pi_prod» := P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_lintegral_pi_prod_752dfe38d72d
