-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_height_eq_of_isMaximal_mvPolynomial_fin_6b75e0ad698e
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_height_eq_of_isMaximal_mvPolynomial_fin_6b75e0ad698e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:10:41.625453+00:00
-- url     : https://prove2.me/theorems/504631b5-259c-45d2-a8dd-96d4b6186386
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR height eq of is Maximal mv Polynomial fin 6b75e0ad698e: P2 M Ground Theory Heights  Heights Numbers DVR height eq of is Maximal mv Polynomial fin 6b75e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR height eq of is Maximal mv Polynomial fin 6b75e0ad698e construction uses the P2 M Ground Theory Heights  Heights Numbers DVR height eq of is Maximal mv Polynomial fin 6b75e0ad698e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMaximalIdealHeightFG.lean#L11-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMaximalIdealHeightFG.lean#L11-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsMaxHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMaximalIdealHeightFG
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
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_height_eq_of_isMaximal_mvPolynomial_fin_6b75e0ad698e (F : Type u) [Field F] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) F)), M.IsMaximal → M.height = n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«height_eq_of_isMaximal_mvPolynomial_fin» := P2M_GroundTheory_Heights__Heights_NumbersDVR_height_eq_of_isMaximal_mvPolynomial_fin_6b75e0ad698e
