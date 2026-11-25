-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_eval_smul
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_eval_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:08:33.109996+00:00
-- url     : https://prove2.me/theorems/1f55cbd2-8f65-592f-bfaa-fd96867730f6
-- title:
--   Arakelov Geometry: gbap eval smul
-- statement:
--   The Arakelov Geometry construction uses the gbap eval smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStB.lean#L231-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/AParamStB.lean#L231-L244

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_eval_smul {ι : Type*} {φ : MvPolynomial ι ℂ} {n : ℕ}
    (hφ : φ.IsHomogeneous n) (c : ℂ) (z : ι → ℂ) :
    eval (c • z) φ = c ^ n * eval z φ := by sorry
