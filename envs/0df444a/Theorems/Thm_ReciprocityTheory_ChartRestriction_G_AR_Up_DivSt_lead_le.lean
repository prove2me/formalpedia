-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_lead_le
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt.lead_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:58:02.056021+00:00
-- url     : https://prove2.me/theorems/81c7c101-96c3-5aee-a7d6-8f5045a041cb
-- title:
--   Div St: lead le
-- statement:
--   The Div St construction uses the lead le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStartPf.lean#L138-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStartPf.lean#L138-L196

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_JetsPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DivStartPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt.lead_le {Xa : ArchInM X} (Fl : FlatM X Xa) {δ : ℕ} (t : Fin δ → Frame X.Ψ r → ℂ) (a0 : ℕ)
    (ha0 : a0 ≤ Xa.T) (cc : (Fin (nd X) → ℕ) → Fin δ → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    {A Ct : ℝ} (hA : 0 ≤ A) (hCt : 0 ≤ Ct) (hs : ∀ q, X.pnorm Xa.L (Fl.s q) x ≤ A)
    (hw : X.pnorm Xa.L Fl.w0 x ≤ A) (ht : ∀ k, X.pnorm Xa.Fp (t k) x ≤ Ct) :
    X.pnorm (Xa.Fp + Xa.T • Xa.L) (leadM X Fl.s Fl.w0 t Xa.T a0 cc) x ≤
      (∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) a0, ∑ k, ‖cc α k‖) * Ct * A ^ Xa.T := by sorry
