-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_PlueckerHadamard_hypotheses_inhabited_af9d0b9b23c8
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_PlueckerHadamard_hypotheses_inhabited_af9d0b9b23c8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:34.806808+00:00
-- url     : https://prove2.me/theorems/d86e8057-de9e-4b4a-af4d-6b2f74e4f97b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Pluecker Hadamard hypotheses inhabited af9d0b9b23c8: P2 M Ground Theory Heights  Heights Rest Terms Pluecker Hadamard hypotheses inhabited af9d0b9b23c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Pluecker Hadamard hypotheses inhabited af9d0b9b23c8 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Pluecker Hadamard hypotheses inhabited af9d0b9b23c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Statements.lean#L417-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Statements.lean#L417-L418

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_PlueckerHadamard_hypotheses_inhabited_af9d0b9b23c8 :
    ∀ i j, ‖(Matrix.of fun (_ : Fin 2) (_ : Fin 3) => (1 : ℂ)) i j‖ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«PlueckerHadamard».«hypotheses_inhabited» := P2M_GroundTheory_Heights__Heights_RestTerms_PlueckerHadamard_hypotheses_inhabited_af9d0b9b23c8
