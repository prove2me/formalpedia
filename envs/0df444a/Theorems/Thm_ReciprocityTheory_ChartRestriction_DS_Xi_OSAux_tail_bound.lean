-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_tail_bound
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.tail_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:27.155616+00:00
-- url     : https://prove2.me/theorems/e953a53a-b72d-4af0-b983-97bb00aa57aa
-- title:
--   OSAux: tail bound
-- statement:
--   The OSAux construction uses the tail bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExponentConditionNeg.lean#L102-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/ExponentConditionNeg.lean#L102-L212

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LintegralInsertFiberLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DeZeroBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExponentConditionNeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.tail_bound (hT : TailFin) (hC1 : C1) (hK : KER) (hL : SLOW) {p m : ℕ} (e : Fin (p + 2) → ℝ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (he : ∀ l, 0 < e l)
    (hsum : e 0 + 2 * ∑ i : Fin (p + 1), e i.succ < γ / 2) :
    ∃ C : ℝ, ∫⁻ x : Xp (p + 1) m, fS (fun l => s0N (p + 1) m l - e l) x * (‖x.2.1 0‖₊ : ℝ≥0∞) ^ (-γ) ≤
      ENNReal.ofReal C := by sorry
