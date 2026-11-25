-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_adens_continuousOn_maDens
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_continuousOn_maDens
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:01.056297+00:00
-- url     : https://prove2.me/theorems/19713b39-f483-4d6a-863e-2abd431f1c58
-- title:
--   Arakelov Geometry: adens continuous On ma Dens
-- statement:
--   The Arakelov Geometry construction uses the adens continuous On ma Dens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L106-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ADensStC.lean#L106-L127

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
open scoped ComplexOrder
variable {J : Type} [Fintype J] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_continuousOn_maDens (φ : Fin D → (Fin D → ℂ) → ℝ) {V : Set (Fin D → ℂ)}
    (hV : IsOpen V) (h : ∀ k, ContDiffOn ℝ 2 (φ k) V) :
    ContinuousOn (ReciprocityTheory.AnForm.maDens φ) V := by sorry
