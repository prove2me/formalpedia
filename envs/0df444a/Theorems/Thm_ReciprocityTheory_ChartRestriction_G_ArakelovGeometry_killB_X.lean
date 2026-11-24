-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_killB_X
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.killB_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:48.106931+00:00
-- url     : https://prove2.me/theorems/4af55101-6aee-4674-8b5e-ca718a8c8818
-- title:
--   Arakelov Geometry: kill B X
-- statement:
--   The Arakelov Geometry construction uses the kill B X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/NotRelevantOfDimZero.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/NotRelevantOfDimZero.lean#L14-L17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HasympAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_NotRelevantOfDimZero
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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.killB_X (T : Finset K) (p : Σ k, ι k) :
    killB T (X p : MRing ι) = if p.1 ∈ T then 0 else X p := by sorry
