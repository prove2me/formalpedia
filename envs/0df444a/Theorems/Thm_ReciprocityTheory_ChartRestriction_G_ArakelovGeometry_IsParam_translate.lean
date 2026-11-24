-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_IsParam_translate
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsParam.translate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:34.712281+00:00
-- url     : https://prove2.me/theorems/6859d039-cfd7-4197-a65b-ba8d776605a5
-- title:
--   Is Param: translate
-- statement:
--   The Is Param construction uses the translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamSt.lean#L128-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamSt.lean#L128-L173

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IsParam.translate {P : Ideal (MvPolynomial (Ix κ) ℤ)} {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → Ix κ → ℂ} (h : IsParam P U γ) (y₀ : Fin D → ℂ) {ρ₀ : ℝ}
    (hball : Metric.ball y₀ ρ₀ ⊆ U) :
    IsParam P (Metric.ball 0 ρ₀) fun y => γ (y₀ + y) := by sorry
