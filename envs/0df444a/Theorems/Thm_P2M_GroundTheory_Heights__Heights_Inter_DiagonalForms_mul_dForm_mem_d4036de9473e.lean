-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mul_dForm_mem_d4036de9473e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mul_dForm_mem_d4036de9473e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:38.623628+00:00
-- url     : https://prove2.me/theorems/044b9fd5-e3a4-4679-b5af-c7e616a585f5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Forms mul d Form mem d4036de9473e: P2 M Ground Theory Heights  Heights Inter Diagonal Forms mul d Form mem d4036de9473e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Forms mul d Form mem d4036de9473e construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Forms mul d Form mem d4036de9473e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L209-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagForms.lean#L209-L232

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
variable {Ω : Type} [Field Ω] {ι κ : Type} {E : Type} [AddCommGroup E] [Module Ω E] {x : ι → Ω}

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mul_dForm_mem_d4036de9473e (B : ChartBundle ℤ x 2 E) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω)
    (hsec : T.IsTwistedDualSec B φ) (i : ι) (hi : x i ≠ 0) (k k' : κ) {y : Ω}
    (hy : y ∈ Submodule.span (chartRing ℤ x i) {d | ∃ u ∈ B.lat i, ∃ w ∈ B.lat i, d = x i * T.detE e u w}) :
    ∃ r ∈ chartRing ℤ x i, y * (φ k (e 0) * φ k' (e 1) - φ k' (e 0) * φ k (e 1)) = x i ^ 3 * r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalForms».«mul_dForm_mem» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalForms_mul_dForm_mem_d4036de9473e
