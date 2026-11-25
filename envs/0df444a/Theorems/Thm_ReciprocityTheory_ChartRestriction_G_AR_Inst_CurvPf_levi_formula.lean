-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Inst_CurvPf_levi_formula
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.levi_formula
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:57:11.384945+00:00
-- url     : https://prove2.me/theorems/f6816658-c599-4785-98d2-52e915ef0913
-- title:
--   Curv Pf: levi formula
-- statement:
--   The Curv Pf construction uses the levi formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/CurvatureStatementHolds.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/CurvatureStatementHolds.lean#L67-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CoefNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CurvatureStatementHolds
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
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Filter Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf.levi_formula (la : Wt X.Ψ r) (x0 : Frame X.Ψ r) (z : V (nd X)) (hz : cpt X x0 z ∈ X.dom)
    (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (ξ : Fin (nd X) → ℂ) :
    (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re =
      ∑ τ, ∑ a : Fin r, ∑ j : Fin r, if (a : ℕ) < j then
        coef X la τ a j * ‖Yd X b z (WithLp.toLp 2 ξ) τ j a‖ ^ 2 else 0 := by sorry
