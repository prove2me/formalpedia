-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_lintegral_insertFiber_le
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.lintegral_insertFiber_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:19.541258+00:00
-- url     : https://prove2.me/theorems/27b0e796-6d01-5d37-857b-47a860c5861f
-- title:
--   OSAux: lintegral insert Fiber le
-- statement:
--   The OSAux construction uses the lintegral insert Fiber le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LintegralInsertFiberLe.lean#L76-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/LintegralInsertFiberLe.lean#L76-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LintegralInsertFiberLe
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.lintegral_insertFiber_le (hC1 : C1) (hK : KER) {e0 γ : ℝ} (he0 : 0 < e0) (hγ : e0 < γ) (hγ2 : γ < 2) :
    ∃ CK : ℝ, 0 < CK ∧ ∀ {p m : ℕ} (y : Yp p m),
      ∫⁻ z : ℂ, ENNReal.ofReal (de (ins y z) 0 ^ (-(2 - e0))) * (‖z‖₊ : ℝ≥0∞) ^ (-γ) ≤
        ENNReal.ofReal (CK * Lsq (tailPt y) 1 ^ (-1 + γ / 2) * de (tailPt y) 0 ^ (-(γ - e0))) := by sorry
