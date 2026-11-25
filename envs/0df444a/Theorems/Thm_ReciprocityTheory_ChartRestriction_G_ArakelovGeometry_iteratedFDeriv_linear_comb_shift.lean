-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_iteratedFDeriv_linear_comb_shift
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.iteratedFDeriv_linear_comb_shift
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:17:17.82781+00:00
-- url     : https://prove2.me/theorems/ebfc24af-0597-5633-8b7a-27dc9d8f83be
-- title:
--   Arakelov Geometry: iterated FDeriv linear comb shift
-- statement:
--   The Arakelov Geometry construction uses the iterated FDeriv linear comb shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsBoundIteratedFDerivCompact.lean#L83-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsBoundIteratedFDerivCompact.lean#L83-L97

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AInterpSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenMet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsBoundIteratedFDerivCompact
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory
open scoped ContDiff

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.iteratedFDeriv_linear_comb_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ₀ ψ₁ : E → ℝ) (y₀ y : E) (k : ℕ) (a₀ a₁ : ℝ)
    (h₀ : ContDiffAt ℝ k ψ₀ (y₀ + y)) (h₁ : ContDiffAt ℝ k ψ₁ (y₀ + y)) :
    iteratedFDeriv ℝ k (fun y => a₀ * ψ₀ (y₀ + y) + a₁ * ψ₁ (y₀ + y)) y =
      a₀ • iteratedFDeriv ℝ k ψ₀ (y₀ + y) + a₁ • iteratedFDeriv ℝ k ψ₁ (y₀ + y) := by sorry
