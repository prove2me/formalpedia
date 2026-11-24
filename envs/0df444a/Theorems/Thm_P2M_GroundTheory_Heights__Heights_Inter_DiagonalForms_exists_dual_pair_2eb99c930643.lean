-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_dual_pair_2eb99c930643
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_dual_pair_2eb99c930643
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:11.199641+00:00
-- url     : https://prove2.me/theorems/a12f5409-03f1-4c09-81f7-3ab2c5ec0740
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists dual pair 2eb99c930643: P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists dual pair 2eb99c930643
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists dual pair 2eb99c930643 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms exists dual pair 2eb99c930643 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L150-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L150-L165

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
variable {Ω : Type*} [Field Ω] {ι : Type*} {E : Type*} [AddCommGroup E] [Module Ω E] {x : ι → Ω}

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_dual_pair_2eb99c930643 (B : ChartBundle ℤ x 2 E) (i : ι) (hi : x i ≠ 0) (e : Module.Basis (Fin 2) Ω E) :
    ∃ ψ₀ ∈ T.dualLat B i, ∃ ψ₁ ∈ T.dualLat B i, ψ₀ (e 0) * ψ₁ (e 1) - ψ₁ (e 0) * ψ₀ (e 1) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«exists_dual_pair» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_exists_dual_pair_2eb99c930643
