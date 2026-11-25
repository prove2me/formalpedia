-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_beta_bound
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.beta_bound
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:48:02.712097+00:00
-- url     : https://prove2.me/theorems/2cdb7e8b-3438-41b5-8c15-65c992498cf0
-- title:
--   OSAux: beta bound
-- statement:
--   The OSAux construction uses the beta bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DeZeroBounds.lean#L111-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/DeZeroBounds.lean#L111-L319

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DeZeroBounds
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

theorem ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.beta_bound (hL : SLOW) {p m : ℕ} (e : Fin (p + 2) → ℝ) {γ : ℝ} (he : ∀ l, 0 < e l)
    (he1 : ∀ l, e l ≤ 1) (hγ2 : γ < 2) (hα : 0 < γ / 2 - e 0) :
    ∃ CS : ℝ, 0 < CS ∧ ∀ (a : Fin (p + 1) → ℂ) (a'' : Fin p → ℂ) (u : Fin m → ℂ),
      ∫⁻ β : ℝ, ENNReal.ofReal (Lsq (tailPt (a, a'', u, β)) 1 ^ (-1 + γ / 2)) *
          ENNReal.ofReal (de (tailPt (a, a'', u, β)) 0 ^ (-(γ - e 0))) *
          ∏ i : Fin (p + 1), ENNReal.ofReal
            (de (tailPt (a, a'', u, β)) i.succ ^ (-(s0N (p + 1) m i.succ - e i.succ))) ≤
        ENNReal.ofReal CS * ∫⁻ β : ℝ,
          ENNReal.ofReal (Lsq (tailPt (a, a'', u, β)) 1 ^ ((-2 + (γ / 2 - e 0)) / 2)) *
          ENNReal.ofReal (de (tailPt (a, a'', u, β)) 1 ^ (-(γ / 2 - e 0))) *
          ∏ i : Fin (p + 1), ENNReal.ofReal (de (tailPt (a, a'', u, β)) i.succ ^
            (-(s0N (p + 1) m i.succ + (fun i : Fin (p + 1) => -e i.succ) i))) := by sorry
