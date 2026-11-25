-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_add_d18806d51dde
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_add_d18806d51dde
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:27.055895+00:00
-- url     : https://prove2.me/theorems/358fc95b-9363-449a-8be7-13275a9bf313
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Pair Expansion add d18806d51dde: P2 M Ground Theory Heights  Heights Numbers DVR is Pair Expansion add d18806d51dde
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Pair Expansion add d18806d51dde construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Pair Expansion add d18806d51dde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L168-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L168-L174

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_add_d18806d51dde {n m : ℕ} {A B : MvPolynomial (Fin n) ℤ}
    {As Bs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ} (hA : IsPairExpansion m A As)
    (hB : IsPairExpansion m B Bs) : IsPairExpansion m (A + B) (As + Bs) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isPairExpansion_add» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_add_d18806d51dde
