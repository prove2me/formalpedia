-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_mem_wwIdeal_of_aeval_eq_zero_25b295e2b105
-- name    : P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_mem_wwIdeal_of_aeval_eq_zero_25b295e2b105
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:28:32.91945+00:00
-- url     : https://prove2.me/theorems/a56a688d-5dba-48b9-89b4-bbc24ad7eec4
-- title:
--   P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame mem ww Ideal of aeval eq zero 25b295e2b105: P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame mem ww Ideal of aeval eq zero 25b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame mem ww Ideal of aeval eq zero 25b295e2b105 construction uses the P2 M Ground Theory Heights  Heights Inter Diagonal Off Frame mem ww Ideal of aeval eq zero 25b295e2b105 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L117-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PDiagOffFrame.lean#L117-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagOffPair
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagOffFrame
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
open GroundTheory.Heights₂.Heights.Inter.DiagonalOffFrame
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E]
  [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_mem_wwIdeal_of_aeval_eq_zero_25b295e2b105 (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E)
    (φ : κ → E →ₗ[Ω] Ω) (a₀ a₁ : Φ) {s : MRing (T.wwIdx ι ν κ)} {β : T.WBlk → ℕ} (hs : IsMultiHomog s β)
    (h : aeval (T.wwCoord x δ e φ a₀ a₁) s = 0) : s ∈ T.wwIdeal x δ e φ a₀ a₁ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«DiagonalOffFrame».«mem_wwIdeal_of_aeval_eq_zero» := P2M_GroundTheory_Heights__Heights_Inter_DiagonalOffFrame_mem_wwIdeal_of_aeval_eq_zero_25b295e2b105
