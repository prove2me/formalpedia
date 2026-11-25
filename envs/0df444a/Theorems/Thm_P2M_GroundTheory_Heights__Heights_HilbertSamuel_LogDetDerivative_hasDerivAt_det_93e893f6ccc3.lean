-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_hasDerivAt_det_93e893f6ccc3
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_hasDerivAt_det_93e893f6ccc3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:51.778567+00:00
-- url     : https://prove2.me/theorems/6547b11c-10fa-482c-b23a-cf4b6c49e4c6
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Log Det Derivative has Deriv At det 93e893f6ccc3: P2 M Ground Theory Heights  Heights Hilbert Samuel Log Det Derivative has Deriv At det 93e893f6ccc3
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Log Det Derivative has Deriv At det 93e893f6ccc3 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Log Det Derivative has Deriv At det 93e893f6ccc3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/HasDerivAtDet.lean#L13-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/HasDerivAtDet.lean#L13-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_HasDerivAtDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Matrix Equiv
open scoped ComplexOrder
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_hasDerivAt_det_93e893f6ccc3 {m : ℕ} {G : ℝ → Matrix (Fin m) (Fin m) ℂ}
    {G' : Matrix (Fin m) (Fin m) ℂ} {t : ℝ} (h : ∀ i j, HasDerivAt (fun s ↦ G s i j) (G' i j) t) :
    HasDerivAt (fun s ↦ (G s).det) (∑ i, (G t).cramer (fun k ↦ G' k i) i) t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«LogDetDerivative».«hasDerivAt_det» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_hasDerivAt_det_93e893f6ccc3
