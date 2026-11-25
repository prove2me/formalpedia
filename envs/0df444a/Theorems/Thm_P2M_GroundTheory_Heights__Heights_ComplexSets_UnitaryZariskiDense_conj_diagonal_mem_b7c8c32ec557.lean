-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_conj_diagonal_mem_b7c8c32ec557
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_conj_diagonal_mem_b7c8c32ec557
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:28.383699+00:00
-- url     : https://prove2.me/theorems/6917c40b-3a0f-4810-9afd-b71d713718eb
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets Unitary Zariski Dense conj diagonal mem b7c8c32ec557: P2 M Ground Theory Heights  Heights Complex Sets Unitary Zariski Dense conj diagonal mem b7c8c32e
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets Unitary Zariski Dense conj diagonal mem b7c8c32ec557 construction uses the P2 M Ground Theory Heights  Heights Complex Sets Unitary Zariski Dense conj diagonal mem b7c8c32ec557 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PUnitaryZariskiDense.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PUnitaryZariskiDense.lean#L39-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUnitaryZariskiDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUnitaryZariskiDense
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
open MvPolynomial Matrix Complex
noncomputable section
open GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_conj_diagonal_mem_b7c8c32ec557 {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ unitaryGroup (Fin n) ℂ)
    {d : Fin n → ℂ} (hd : ∀ k, ‖d k‖ = 1) : V * diagonal d * star V ∈ unitaryGroup (Fin n) ℂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«UnitaryZariskiDense».«conj_diagonal_mem» := P2M_GroundTheory_Heights__Heights_ComplexSets_UnitaryZariskiDense_conj_diagonal_mem_b7c8c32ec557
