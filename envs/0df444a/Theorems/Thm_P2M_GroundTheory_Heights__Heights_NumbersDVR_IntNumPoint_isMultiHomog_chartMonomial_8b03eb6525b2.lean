-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_isMultiHomog_chartMonomial_8b03eb6525b2
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_isMultiHomog_chartMonomial_8b03eb6525b2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:28.8488+00:00
-- url     : https://prove2.me/theorems/e50a45d4-2a7b-4c8c-95c0-53e9a3c60806
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point is Multi Homog chart Monomial 8b03eb6525b2: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point is Multi Homog chart Monomial 8b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point is Multi Homog chart Monomial 8b03eb6525b2 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point is Multi Homog chart Monomial 8b03eb6525b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L22-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
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
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_isMultiHomog_chartMonomial_8b03eb6525b2 (i : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) i e) e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumPoint».«isMultiHomog_chartMonomial» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_isMultiHomog_chartMonomial_8b03eb6525b2
