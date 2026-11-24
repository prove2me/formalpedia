-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_push_f1807b2e66f9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_push_f1807b2e66f9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:37:27.862811+00:00
-- url     : https://prove2.me/theorems/39ba669a-98a8-4c22-b37e-3d2972a7dc57
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Pair Expansion push f1807b2e66f9: P2 M Ground Theory Heights  Heights Numbers DVR is Pair Expansion push f1807b2e66f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Pair Expansion push f1807b2e66f9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Pair Expansion push f1807b2e66f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L176-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L176-L190

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_push_f1807b2e66f9 {n n' m : ℕ} (σ : Fin n → Fin n') {A : MvPolynomial (Fin n) ℤ}
    {Gs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ} (h : IsPairExpansion m A Gs) :
    IsPairExpansion m (rename σ A) (pushExpansion σ Gs) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isPairExpansion_push» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_push_f1807b2e66f9
