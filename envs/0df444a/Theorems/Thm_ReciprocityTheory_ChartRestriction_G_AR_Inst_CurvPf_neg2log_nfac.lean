-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_neg2log_nfac
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.neg2log_nfac
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:27:48.77901+00:00
-- url     : https://prove2.me/theorems/77c22794-8460-42dd-91bd-bc59ae979ff2
-- title:
--   Curv Pf: neg2log nfac
-- statement:
--   The Curv Pf construction uses the neg2log nfac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LeviFinsetSum.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/LeviFinsetSum.lean#L13-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetSubMapConj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_LeviFinsetSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.AnForm Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.neg2log_nfac (la : Wt X.Ψ r) (x : Frame X.Ψ r) (hx : ∀ τ i, dmin X.Gm x τ i ≠ 0) :
    -2 * Real.log (X.nfac la x) = ∑ τ, ∑ i : Fin r, (la τ i : ℝ) *
      (Real.log ‖dmin X.Gm x τ i.succ‖ - Real.log ‖dmin X.Gm x τ i.castSucc‖) := by sorry
