-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_le_of_tdeg_le
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.le_of_tdeg_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:36.56626+00:00
-- url     : https://prove2.me/theorems/0c136fd9-0dd3-4b98-8583-23bb1b057745
-- title:
--   Arakelov Geometry: le of tdeg le
-- statement:
--   The Arakelov Geometry construction uses the le of tdeg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/DimOfMinimal.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/DimOfMinimal.lean#L57-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogX
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DimOfMinimal
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.le_of_tdeg_le {c a : K → ℕ} {a₀ : ℕ} (ha : ∀ k, a₀ + tdeg c ≤ a k) (k : K) :
    c k ≤ a k ∧ a₀ ≤ (a - c) k := by sorry
