-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_smul_mem_pts
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_smul_mem_pts
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:05:41.405246+00:00
-- url     : https://prove2.me/theorems/1a1e2f2f-5eeb-5345-bf64-d6eed25b7139
-- title:
--   Arakelov Geometry: gbap smul mem pts
-- statement:
--   The Arakelov Geometry construction uses the gbap smul mem pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStB.lean#L246-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStB.lean#L246-L253

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_ExistsAnalyticGraphChartMvPolynomial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {Ω : Type} [Field Ω] [CharZero Ω]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_smul_mem_pts {J : Type} [Fintype J] (x : J → Ω) {z : J → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) {c : ℂ} (hc : c ≠ 0) : c • z ∈ pts (coordIdeal ℤ x) := by sorry
