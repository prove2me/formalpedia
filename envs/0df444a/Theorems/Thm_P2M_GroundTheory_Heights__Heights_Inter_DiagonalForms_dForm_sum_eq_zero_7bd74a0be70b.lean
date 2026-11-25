-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_dForm_sum_eq_zero_7bd74a0be70b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_dForm_sum_eq_zero_7bd74a0be70b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:34.141232+00:00
-- url     : https://prove2.me/theorems/934544e1-d8f5-4b50-b170-3dfa8214f48c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms d Form sum eq zero 7bd74a0be70b: P2 M Ground Theory Heights  Heights Inter Diagonal Forms d Form sum eq zero 7bd74a0be70b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms d Form sum eq zero 7bd74a0be70b construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms d Form sum eq zero 7bd74a0be70b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L191-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L191-L201

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalForms
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_dForm_sum_eq_zero_7bd74a0be70b {κ : Type*} [Fintype κ] (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (hd : ∀ k k', φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1) = 0) (c c' : κ → Ω) (s : Ω) :
    (∑ k, c k • s • φ k) (e 0) * (∑ k, c' k • s • φ k) (e 1) -
      (∑ k, c' k • s • φ k) (e 0) * (∑ k, c k • s • φ k) (e 1) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«dForm_sum_eq_zero» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_dForm_sum_eq_zero_7bd74a0be70b
