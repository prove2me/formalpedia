-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_hon_series
-- name    : ReciprocityTheory.ChartRestriction.L1.hon_series
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:46:20.316028+00:00
-- url     : https://prove2.me/theorems/a3e5504d-8f86-52bb-a435-82821e17915c
-- title:
--   L1: hon series
-- statement:
--   The L1 construction uses the hon series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonF.lean#L166-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonF.lean#L166-L220

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SubstOfLog
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}

theorem ReciprocityTheory.ChartRestriction.L1.hon_series (hF : FrobField K l σ) (h : HD σ lam Φ A a) {e : PowerSeries K}
    (he0 : constantCoeff e = 0) (he : IntegralPS e) (hlog : lam.subst e = C (l : K) * lam)
    (hlev : ∃ i, i ≤ l ^ 2 ∧ ‖coeff i e‖ = 1) :
    ∃ c : ℕ → K, ‖c 0‖ = 1 ∧ (∀ i, ‖c i‖ ≤ 1) ∧ ∀ N : ℕ, ∃ R : PowerSeries K,
      constantCoeff R = 0 ∧
      DivBy (l : K) (C (l : K) * lam
        - ∑ i ∈ Finset.range N, C (c i) *
            (PowerSeries.map ((σ.comp σ) ^ (i + 1)) lam).subst
              ((X : PowerSeries K) ^ ((l ^ 2) ^ (i + 1)))
        - R.subst ((X : PowerSeries K) ^ ((l ^ 2) ^ (N + 1)))) := by sorry
