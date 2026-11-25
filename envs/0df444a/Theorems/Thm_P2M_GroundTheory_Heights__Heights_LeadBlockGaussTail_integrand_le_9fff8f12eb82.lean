-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_integrand_le_9fff8f12eb82
-- name    : P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_integrand_le_9fff8f12eb82
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:40.389588+00:00
-- url     : https://prove2.me/theorems/a1551569-add2-4ef1-8885-d97480f6fc9b
-- title:
--   P2 M Ground Theory Heights  Heights Lead Block Gauss Tail integrand le 9fff8f12eb82: P2 M Ground Theory Heights  Heights Lead Block Gauss Tail integrand le 9fff8f12eb82
-- statement:
--   The P2 M Ground Theory Heights  Heights Lead Block Gauss Tail integrand le 9fff8f12eb82 construction uses the P2 M Ground Theory Heights  Heights Lead Block Gauss Tail integrand le 9fff8f12eb82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L215-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L215-L250

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

theorem P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_integrand_le_9fff8f12eb82 {m k : ℕ} (hm : 0 < m) (r : ℝ) (π : Fin m → Fin (m + k) → ℂ) :
    matGauss π * (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
        (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
        ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) ≤
      ENNReal.ofReal (Fintype.card (Equiv.Perm (Fin m))) * ∑ σ : Equiv.Perm (Fin m),
        ∏ i, ∏ j, entryFn r (Fin.castAdd k ⟨0, hm⟩) (Fin.castAdd k (σ i)) j (π i j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LeadBlockGaussTail».«integrand_le» := P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_integrand_le_9fff8f12eb82
