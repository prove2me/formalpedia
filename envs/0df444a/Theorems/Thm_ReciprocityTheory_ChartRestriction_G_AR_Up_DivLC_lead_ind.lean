-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DivLC_lead_ind
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC.lead_ind
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:05.576162+00:00
-- url     : https://prove2.me/theorems/428ad9d1-b500-520d-aa3c-710dba340a41
-- title:
--   Div LC: lead ind
-- statement:
--   The Div LC construction uses the lead ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLE.lean#L64-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DivStatementPfLE.lean#L64-L119

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC.lead_ind {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) {δ : ℕ}
    (t : Fin δ → Frame X.Ψ r → ℂ) (ht : ∀ k, X.IsSec Xa.Fp (t k)) (hval : IsValBasisM X Fl.xs t)
    (f : Frame X.Ψ r → ℂ) (hf : X.IsSec (Xa.Fp + Xa.T • Xa.L) f) :
    ∀ d, d ≤ Xa.T → ∃ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ, ∀ j,
      (fun z => f (cpt X (Fl.xs j) z) - leadM X Fl.s Fl.w0 t Xa.T d cc (cpt X (Fl.xs j) z)) =O[𝓝 0]
        fun z => ‖z‖ ^ d := by sorry
