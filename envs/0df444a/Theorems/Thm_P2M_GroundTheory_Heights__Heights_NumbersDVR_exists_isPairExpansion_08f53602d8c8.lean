-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_isPairExpansion_08f53602d8c8
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_isPairExpansion_08f53602d8c8
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:43.963042+00:00
-- url     : https://prove2.me/theorems/8b8d0ec7-e9a2-422f-a19d-74926eb8ebd4
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists is Pair Expansion 08f53602d8c8: P2 M Ground Theory Heights  Heights Numbers DVR exists is Pair Expansion 08f53602d8c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists is Pair Expansion 08f53602d8c8 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists is Pair Expansion 08f53602d8c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L240-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L240-L257

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_isPairExpansion_08f53602d8c8 {n m : ℕ} {A : MvPolynomial (Fin n) ℤ} (hA : A.IsHomogeneous m) :
    ∃ Gs, IsPairExpansion m A Gs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_isPairExpansion» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_isPairExpansion_08f53602d8c8
