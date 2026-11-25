-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_line_dim_69b0ee92cc8e
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_line_dim_69b0ee92cc8e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:29.014921+00:00
-- url     : https://prove2.me/theorems/05f30496-5822-5f24-b869-cc4f7b8657f1
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets line dim 69b0ee92cc8e: P2 M Ground Theory Heights  Heights Complex Sets line dim 69b0ee92cc8e
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets line dim 69b0ee92cc8e construction uses the P2 M Ground Theory Heights  Heights Complex Sets line dim 69b0ee92cc8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/Statements.lean#L97-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
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
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_line_dim_69b0ee92cc8e : ringKrullDim (MvPolynomial (Fin 1) ℂ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℂ))) =
    (1 : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«line_dim» := P2M_GroundTheory_Heights__Heights_ComplexSets_line_dim_69b0ee92cc8e
