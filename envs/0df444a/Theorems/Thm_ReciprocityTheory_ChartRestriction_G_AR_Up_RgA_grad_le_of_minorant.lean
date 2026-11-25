-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgA_grad_le_of_minorant
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.RgA.grad_le_of_minorant
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:08.292113+00:00
-- url     : https://prove2.me/theorems/25ef15a2-03e4-5c17-891b-98834e52b55d
-- title:
--   Rg A: grad le of minorant
-- statement:
--   The Rg A construction uses the grad le of minorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradStatementPfA.lean#L12-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradStatementPfA.lean#L12-L86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfA
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RgA
open Topology Filter
open ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.RgA.grad_le_of_minorant (rh Ψ : V n → ℝ) (v0 : V n) (C : ℝ) (hC : 0 < C)
    (hΨ0 : 0 < Ψ v0) (hrh : ContDiffAt ℝ 2 rh v0) (hΨ : ContDiffAt ℝ 2 Ψ v0) (ξ : Fin n → ℂ)
    (hL : (leviV n (fun y => (Ψ y : ℂ)) v0 ξ).re ≤ 0)
    (hle : ∀ᶠ v in 𝓝 v0, -C * Real.log (Ψ v) ≤ rh v) (heq : rh v0 = -C * Real.log (Ψ v0)) :
    Complex.normSq (∑ j, wd n j (fun y => (rh y : ℂ)) v0 * ξ j) ≤
      C * (leviV n (fun y => (rh y : ℂ)) v0 ξ).re := by sorry
