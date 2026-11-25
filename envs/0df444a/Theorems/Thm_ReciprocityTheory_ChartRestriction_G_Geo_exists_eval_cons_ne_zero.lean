-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_eval_cons_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.exists_eval_cons_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:28:30.926699+00:00
-- url     : https://prove2.me/theorems/70afaf76-f17c-5871-80ea-5bf4418ae12e
-- title:
--   Geo: exists eval cons ne zero
-- statement:
--   The Geo construction uses the exists eval cons ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeO.lean#L32-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeO.lean#L32-L54

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeJ
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
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
open MvPolynomial MeasureTheory

theorem ReciprocityTheory.ChartRestriction.G.Geo.exists_eval_cons_ne_zero {n : ℕ} {c : MvPolynomial (Fin (n + 1)) ℂ} {m : ℕ}
    (hc0 : c ≠ 0) (hc : c.IsHomogeneous m) : ∃ y : Fin n → ℂ, eval (Fin.cons 1 y) c ≠ 0 := by sorry
