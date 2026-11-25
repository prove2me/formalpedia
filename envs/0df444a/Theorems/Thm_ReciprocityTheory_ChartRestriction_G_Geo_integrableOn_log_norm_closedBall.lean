-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_integrableOn_log_norm_closedBall
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.integrableOn_log_norm_closedBall
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:23:53.347905+00:00
-- url     : https://prove2.me/theorems/be1ccf88-f051-4bc4-85db-978f974ce08b
-- title:
--   Geo: integrable On log norm closed Ball
-- statement:
--   The Geo construction uses the integrable On log norm closed Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeN.lean#L91-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeN.lean#L91-L183

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

theorem ReciprocityTheory.ChartRestriction.G.Geo.integrableOn_log_norm_closedBall {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    {f : (Fin D → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f U) {z0 : Fin D → ℂ} {t : ℝ} (ht : 0 < t)
    (hS2 : ball z0 (2 * t) ⊆ U) (hz0 : f z0 ≠ 0) :
    IntegrableOn (fun z => Real.log ‖f z‖) (closedBall z0 t) := by sorry
