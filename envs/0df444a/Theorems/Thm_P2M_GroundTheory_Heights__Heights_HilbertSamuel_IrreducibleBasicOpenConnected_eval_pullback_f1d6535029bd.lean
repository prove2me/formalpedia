-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_eval_pullback_f1d6535029bd
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_eval_pullback_f1d6535029bd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:18.189121+00:00
-- url     : https://prove2.me/theorems/1d6561b6-57c6-4ed4-a085-87680934bf2b
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected eval pullback f1d6535029bd: P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected eval
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected eval pullback f1d6535029bd construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Irreducible Basic Open Connected eval pullback f1d6535029bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/BasicOpenSteps.lean#L10-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/IrreducibleConnected/BasicOpenSteps.lean#L10-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_BasicOpenSteps
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
open MvPolynomial Filter Topology

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_eval_pullback_f1d6535029bd {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ)
    (P : MvPolynomial (Fin d) ℂ) (x : Fin n → ℂ) :
    eval x (ComplexSets.pullback A P) = eval (A.mulVec x) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«IrreducibleBasicOpenConnected».«eval_pullback» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_eval_pullback_f1d6535029bd
