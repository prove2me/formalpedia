-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_Base0_psi_le
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.Base0.psi_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:46:49.878806+00:00
-- url     : https://prove2.me/theorems/d7699522-2f2c-4b13-9100-0a10a1f726f0
-- title:
--   Base0: psi le
-- statement:
--   The Base0 construction uses the psi le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IntegrableUnitIndicator.lean#L193-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IntegrableUnitIndicator.lean#L193-L340

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.ChartRestriction.DS.Xi.Base0.psi_le {p q : ι} (hpq : p ≠ q) {k : ℕ} (hk : Fintype.card ι = k + 1) (hk1 : 1 ≤ k) {s : ℝ}
    (hs : 0 ≤ s) {x : ι → ℂ} (hx : x ∈ Bset q) (hg : ∀ i, (x i).im ≠ 0 ∧ (x i).re ≠ 0) :
    PsiF p q s x ≤ ENNReal.ofReal (∏ i, gF p q (s / k) i (x i)) := by sorry
