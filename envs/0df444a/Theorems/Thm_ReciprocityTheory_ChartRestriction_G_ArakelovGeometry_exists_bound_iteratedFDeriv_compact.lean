-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_exists_bound_iteratedFDeriv_compact
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_bound_iteratedFDeriv_compact
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:34.57436+00:00
-- url     : https://prove2.me/theorems/48c128f1-ec14-59bf-b63a-d4e21c173cb6
-- title:
--   Arakelov Geometry: exists bound iterated FDeriv compact
-- statement:
--   The Arakelov Geometry construction uses the exists bound iterated FDeriv compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsBoundIteratedFDerivCompact.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ExistsBoundIteratedFDerivCompact.lean#L57-L63

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_bound_iteratedFDeriv_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {U K : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hK : IsCompact K)
    (hKU : K ⊆ U) (k : ℕ) : ∃ B, 0 ≤ B ∧ ∀ y ∈ K, ‖iteratedFDeriv ℝ k f y‖ ≤ B := by sorry
