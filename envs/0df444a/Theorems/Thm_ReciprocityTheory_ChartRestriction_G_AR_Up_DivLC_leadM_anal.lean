-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLC_leadM_anal
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC.leadM_anal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:58:37.396814+00:00
-- url     : https://prove2.me/theorems/263b8608-e89c-5a63-b750-e55091885546
-- title:
--   Div LC: lead M anal
-- statement:
--   The Div LC construction uses the lead M anal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLE.lean#L45-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLE.lean#L45-L62

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC.leadM_anal {r : ℕ} (X : Data E r) {Xa : ArchInM X} (Fl : FlatM X Xa) {δ : ℕ}
    (t : Fin δ → Frame X.Ψ r → ℂ) (ht : ∀ k, DifferentiableOn ℂ (t k) X.dom) (T d : ℕ)
    (cc : (Fin (nd X) → ℕ) → Fin δ → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    AnalyticAt ℂ (fun z => leadM X Fl.s Fl.w0 t T d cc (cpt X x z)) 0 := by sorry
