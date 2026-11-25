-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_sep_diff
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_sep_diff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:00:37.314742+00:00
-- url     : https://prove2.me/theorems/8302fc36-1bf7-4612-8f10-e26ba4e84573
-- title:
--   Up: sum Bd sep diff
-- statement:
--   The Up construction uses the sum Bd sep diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfB.lean#L108-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfB.lean#L108-L129

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_sep_diff {g h : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hg : IsUpq g) {R c : ℝ}
    (hR : 0 < R) (hc0 : 0 < c) (hgR : ∀ i j, ‖g i j‖ ≤ R) {i j : Fin p ⊕ Fin q}
    (hc : c ≤ ‖(h * g⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖) :
    ∃ l, c / (((p + q : ℕ) : ℝ) + 1) / R ≤ ‖h i l - g i l‖ := by sorry
