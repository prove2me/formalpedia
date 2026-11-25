-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_linear_injOn_5abfc7a649f0
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_linear_injOn_5abfc7a649f0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:12.335517+00:00
-- url     : https://prove2.me/theorems/6a6c6ad7-b45e-461d-9043-7a997610f600
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Fibre Bound exists linear inj On 5abfc7a649f0: P2 M Ground Theory Heights  Heights Complex Sets Fibre Bound exists linear inj On 5abfc7a649f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Fibre Bound exists linear inj On 5abfc7a649f0 construction uses the P2 M Ground Theory Heights  Heights Complex Sets Fibre Bound exists linear inj On 5abfc7a649f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreBound.lean#L23-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFibreBound.lean#L23-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
variable {n d : ℕ}
open GroundTheory.Heights₂.Heights.ComplexSets.FibreBound

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_linear_injOn_5abfc7a649f0 (T : Finset (Fin n → ℂ)) :
    ∃ c : Fin n → ℂ, Set.InjOn (fun x : Fin n → ℂ => ∑ j, c j * x j) T := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«FibreBound».«exists_linear_injOn» := P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_exists_linear_injOn_5abfc7a649f0
