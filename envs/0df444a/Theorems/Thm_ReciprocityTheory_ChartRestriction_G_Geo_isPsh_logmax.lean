-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isPsh_logmax
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.isPsh_logmax
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:24:14.174557+00:00
-- url     : https://prove2.me/theorems/7d47e398-1175-4f11-9414-cae07aab7eb1
-- title:
--   Geo: is Psh logmax
-- statement:
--   The Geo construction uses the is Psh logmax property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeN.lean#L50-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeN.lean#L50-L89

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Metric Filter Topology Real

theorem ReciprocityTheory.ChartRestriction.G.Geo.isPsh_logmax {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) {f : (Fin D → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ReciprocityTheory.AnForm.A.IsPsh U (fun z => Real.log (max ‖f z‖ ε)) := by sorry
