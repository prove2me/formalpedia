-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLA_multilinear_expand
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.multilinear_expand
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:58:43.669777+00:00
-- url     : https://prove2.me/theorems/453425ac-abb8-42b8-a37f-b79432134d81
-- title:
--   Div LA: multilinear expand
-- statement:
--   The Div LA construction uses the multilinear expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLA.lean#L88-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLA.lean#L88-L133

import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStatementPfLA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.multilinear_expand {n d : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin d => V n) ℂ)
    (L : V n ≃L[ℂ] V n) :
    ∃ a : (Fin n → ℕ) → ℂ, ∀ z, q (fun _ => z) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple n d, a α * ∏ k, (L z) k ^ α k := by sorry
