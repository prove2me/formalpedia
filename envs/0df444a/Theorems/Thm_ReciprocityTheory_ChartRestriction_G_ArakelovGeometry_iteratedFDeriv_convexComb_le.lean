-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_iteratedFDeriv_convexComb_le
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.iteratedFDeriv_convexComb_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:15:37.344997+00:00
-- url     : https://prove2.me/theorems/718fb641-bb51-54be-8d7e-d758d6513420
-- title:
--   Arakelov Geometry: iterated FDeriv convex Comb le
-- statement:
--   The Arakelov Geometry construction uses the iterated FDeriv convex Comb le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsBoundIteratedFDerivCompact.lean#L99-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsBoundIteratedFDerivCompact.lean#L99-L117

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.iteratedFDeriv_convexComb_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ₀ ψ₁ : E → ℝ) (y₀ y : E) (k : ℕ) {t B₀ B₁ : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ContDiffAt ℝ k ψ₀ (y₀ + y)) (h₁ : ContDiffAt ℝ k ψ₁ (y₀ + y))
    (hb₀ : ‖iteratedFDeriv ℝ k ψ₀ (y₀ + y)‖ ≤ B₀) (hb₁ : ‖iteratedFDeriv ℝ k ψ₁ (y₀ + y)‖ ≤ B₁) :
    ‖iteratedFDeriv ℝ k (fun y => (2 * (1 - t)) * ψ₀ (y₀ + y) + (2 * t) * ψ₁ (y₀ + y)) y‖ ≤
      2 * (B₀ + B₁) := by sorry
