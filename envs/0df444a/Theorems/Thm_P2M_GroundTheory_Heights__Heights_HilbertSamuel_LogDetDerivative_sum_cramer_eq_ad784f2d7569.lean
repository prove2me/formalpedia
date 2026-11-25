-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_sum_cramer_eq_ad784f2d7569
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_sum_cramer_eq_ad784f2d7569
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:43.021362+00:00
-- url     : https://prove2.me/theorems/630b5eb1-e34f-5293-a32f-fc60cc6e339a
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Log Det Derivative sum cramer eq ad784f2d7569: P2 M Ground Theory Heights  Heights Hilbert Samuel Log Det Derivative sum cramer eq ad784f2d7569
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Log Det Derivative sum cramer eq ad784f2d7569 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Log Det Derivative sum cramer eq ad784f2d7569 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/HasDerivAtDet.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/HasDerivAtDet.lean#L42-L46

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_sum_cramer_eq_ad784f2d7569 {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ)
    (hA : IsUnit A.det) :
    ∑ i, A.cramer (fun k ↦ B k i) i = A.det * (A⁻¹ * B).trace := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«LogDetDerivative».«sum_cramer_eq» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_sum_cramer_eq_ad784f2d7569
