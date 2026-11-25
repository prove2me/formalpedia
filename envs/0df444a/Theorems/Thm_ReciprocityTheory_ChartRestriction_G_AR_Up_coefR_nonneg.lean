-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_coefR_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.coefR_nonneg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:19.624963+00:00
-- url     : https://prove2.me/theorems/0726335e-540f-5bb9-8896-561c3d1bed81
-- title:
--   Up: coef R nonneg
-- statement:
--   The Up construction uses the coef R nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CurvNumStatementPf.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/CurvNumStatementPf.lean#L18-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_CurvatureStatementHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CurvNumStatementPf
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf ReciprocityTheory.L2DbarEstimates Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.coefR_nonneg {r : ℕ} (X : Data E r) (v : X.Ψ → Fin r → ℝ) (hv : IsDominantR X v) (τ : X.Ψ)
    (a j : Fin r) (h : (a : ℕ) < j) : 0 ≤ coefR X v τ a j := by sorry
