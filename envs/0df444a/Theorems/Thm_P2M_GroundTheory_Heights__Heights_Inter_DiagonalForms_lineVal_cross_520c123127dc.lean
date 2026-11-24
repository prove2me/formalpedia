-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_lineVal_cross_520c123127dc
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_lineVal_cross_520c123127dc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:14.704593+00:00
-- url     : https://prove2.me/theorems/2db82bda-3d21-42a4-9622-b6c97a442dc3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms line Val cross 520c123127dc: P2 M Ground Theory Heights  Heights Inter Diagonal Forms line Val cross 520c123127dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms line Val cross 520c123127dc construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms line Val cross 520c123127dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L184-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L184-L189

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

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_lineVal_cross_520c123127dc {Φ : Type*} [Field Φ] [Algebra Ω Φ] (e : Module.Basis (Fin 2) Ω E) (ψ ψ' : E →ₗ[Ω] Ω)
    (a₀ a₁ : Φ) :
    T.lineVal e ψ a₀ * T.lineVal e ψ' a₁ - T.lineVal e ψ' a₀ * T.lineVal e ψ a₁ =
      algebraMap Ω Φ (ψ (e 0) * ψ' (e 1) - ψ' (e 0) * ψ (e 1)) * (a₁ - a₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«lineVal_cross» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_lineVal_cross_520c123127dc
