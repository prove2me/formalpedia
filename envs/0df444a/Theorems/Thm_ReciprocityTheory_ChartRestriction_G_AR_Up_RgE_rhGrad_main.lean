-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgE_rhGrad_main
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.RgE.rhGrad_main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:17:48.632211+00:00
-- url     : https://prove2.me/theorems/cf37259a-9cb5-45a4-979d-1d408be35c8f
-- title:
--   Rg E: rh Grad main
-- statement:
--   The Rg E construction uses the rh Grad main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradStatementPf.lean#L55-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradStatementPf.lean#L55-L166

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPf
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RgE
open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
variable {f p q : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.RgE.rhGrad_main (hf : 0 < f) (hm : 0 < min p q) (v0 : V (nD f p q)) (hv0 : v0 ∈ Dset f p q)
    (ξ : Fin (nD f p q) → ℂ) :
    Complex.normSq (∑ j, wd (nD f p q) j (fun w => ((rh w : ℝ) : ℂ)) v0 * ξ j) ≤
      ((f * min p q : ℕ) : ℝ) * (leviV (nD f p q) (fun w => ((rh w : ℝ) : ℂ)) v0 ξ).re := by sorry
