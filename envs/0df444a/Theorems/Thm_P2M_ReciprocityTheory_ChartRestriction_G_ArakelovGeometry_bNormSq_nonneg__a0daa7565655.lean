-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_bNormSq_nonneg__a0daa7565655
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_bNormSq_nonneg__a0daa7565655
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:35:20.328392+00:00
-- url     : https://prove2.me/theorems/ae20f7af-6293-53f8-a92f-706f99c917b6
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry b Norm Sq nonneg  a0daa7565655: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry b Norm Sq nonneg  a0daa7565655
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry b Norm Sq nonneg  a0daa7565655 construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry b Norm Sq nonneg  a0daa7565655 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStC.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStC.lean#L12-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_bNormSq_nonneg__a0daa7565655 (μ : Measure (Ix κ → ℂ)) (m : ConeMetric ℂ (Ix κ)) {r n : ℕ}
    (s : Fin r → (Ix κ → ℂ) → ℂ) (c : Fin r → ℂ) : 0 ≤ bNormSq μ s (wgt m n) c := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«bNormSq_nonneg'» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_bNormSq_nonneg__a0daa7565655
