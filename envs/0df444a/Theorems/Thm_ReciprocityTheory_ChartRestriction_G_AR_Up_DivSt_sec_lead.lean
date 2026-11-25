-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivSt_sec_lead
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt.sec_lead
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:09:11.798176+00:00
-- url     : https://prove2.me/theorems/97e9908c-642e-5cc9-af73-f5a71c64a766
-- title:
--   Div St: sec lead
-- statement:
--   The Div St construction uses the sec lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStartPf.lean#L88-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStartPf.lean#L88-L107

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivSt.sec_lead {Xa : ArchInM X} (Fl : FlatM X Xa) {δ : ℕ} (t : Fin δ → Frame X.Ψ r → ℂ)
    (ht : ∀ k, X.IsSec Xa.Fp (t k)) (hs : ∀ k, X.IsSec Xa.L (Fl.s k)) (hw : X.IsSec Xa.L Fl.w0)
    (a0 : ℕ) (ha0 : a0 ≤ Xa.T) (cc : (Fin (nd X) → ℕ) → Fin δ → ℂ) :
    X.IsSec (Xa.Fp + Xa.T • Xa.L) (leadM X Fl.s Fl.w0 t Xa.T a0 cc) := by sorry
