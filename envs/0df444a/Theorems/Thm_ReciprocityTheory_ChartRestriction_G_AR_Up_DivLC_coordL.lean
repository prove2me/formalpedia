-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLC_coordL
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC.coordL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:38.397341+00:00
-- url     : https://prove2.me/theorems/2e68f742-a20b-440b-be03-9e5d2bb905fa
-- title:
--   Div LC: coord L
-- statement:
--   The Div LC construction uses the coord L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLE.lean#L12-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLE.lean#L12-L41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC.coordL {n : ℕ} (W : V n → ℂ) (S : Fin n → V n → ℂ) (hW : AnalyticAt ℂ W 0) (hW0 : W 0 ≠ 0)
    (hS : ∀ k, AnalyticAt ℂ (S k) 0) (hS0 : ∀ k, S k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => S k z / W z : V n)) 0).det ≠ 0) :
    ∃ L : V n ≃L[ℂ] V n, (∀ k z, (L z) k = fderiv ℂ (fun y => S k y / W y) 0 z) ∧
      (fun z => (WithLp.toLp 2 fun k => S k z / W z : V n) - L z) =o[𝓝 0] fun z => z := by sorry
