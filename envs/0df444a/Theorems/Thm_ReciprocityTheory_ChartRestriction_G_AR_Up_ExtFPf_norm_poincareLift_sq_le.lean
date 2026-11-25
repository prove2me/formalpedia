-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExtFPf_norm_poincareLift_sq_le
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.norm_poincareLift_sq_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:58:12.879096+00:00
-- url     : https://prove2.me/theorems/92d68c2f-66ec-5008-b641-54d4ab34bc9c
-- title:
--   Ext FPf: norm poincare Lift sq le
-- statement:
--   The Ext FPf construction uses the norm poincare Lift sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExtFStatementPfB.lean#L186-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExtFStatementPfB.lean#L186-L201

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.norm_poincareLift_sq_le {x : Frame X.Ψ r} (_hx : x ∈ X.dom) {m : ℝ} (hm : 0 < m) (hmx : m ≤ X.nfac la x) :
    ENNReal.ofReal (‖P0 D la F x‖ ^ 2) ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * Gf D la F x := by sorry
