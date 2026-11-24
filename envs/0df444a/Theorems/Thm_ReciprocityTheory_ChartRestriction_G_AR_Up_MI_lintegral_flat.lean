-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lintegral_flat
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lintegral_flat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:21.018096+00:00
-- url     : https://prove2.me/theorems/07471747-f331-4250-b657-0364962c5949
-- title:
--   MI: lintegral flat
-- statement:
--   The MI construction uses the lintegral flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfF.lean#L87-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/MeasInvStatementPfF.lean#L87-L111

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix MeasureTheory
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lintegral_flat {g : (Ix ι r → ℂ) → ENNReal} (hg : Measurable g) :
    ∫⁻ v, g v = ∫⁻ x, ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then
      ENNReal.ofReal (Complex.normSq (jacU y)) * g (lu ((eS ι r).symm (x, y))) else 0) := by sorry
