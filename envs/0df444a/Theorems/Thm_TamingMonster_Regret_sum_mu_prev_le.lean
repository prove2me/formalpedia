-- Prove2me | Theorems.Thm_TamingMonster_Regret_sum_mu_prev_le
-- name    : TamingMonster.Regret.sum_mu_prev_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T09:01:37.412047+00:00
-- url     : https://prove2.me/theorems/79c19d6c-e55a-46df-819d-02d2c248bb92
-- title:
--   Lemma 16 — $\sum_{t=1}^T\mu_{m(t)-1}\le\tau_{m_0}/(2K)+\sqrt{8d_{\tau_{m(T)}}\tau_{m(T)}/K}$
-- statement:
--   With the notation of Lemma 15, assume in addition the epoch schedule condition $\tau_{m+1}\le2\tau_m$ for all $m\ge1$, and let $m_0=\min\{m\ge1:d_{\tau_m}/\tau_m\le1/(4K)\}$. For every $T\in\mathbb N$,
--   $$\sum_{t=1}^T\mu_{m(t)-1}\le\frac{\tau_{m_0}}{2K}+\sqrt{\frac{8d_{\tau_{m(T)}}\,\tau_{m(T)}}{K}}.$$
--
--   The left side is the total exploration level actually used by the algorithm (round $t$ samples with $\mu_{m(t)-1}$), which Lemma 14 multiplies by $(4\psi+c_0)K$.
--
--   **Formalization Note** $\mu_0=1/(2K)$, the convention of the Setting file.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 21, Lemma 16

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

namespace TamingMonster.Regret

open MeasureTheory

/-- Lemma 16, p. 21. Under the schedule condition `τ_{m+1} ≤ 2τ_m` (`m ≥ 1`), for every `T`,
`∑_{t=1}^T μ_{m(t)−1} ≤ τ_{m₀}/(2K) + √(8 d_{τ_{m(T)}} τ_{m(T)}/K)` (with `μ_0 = 1/(2K)`). -/
theorem sum_mu_prev_le {X : Type*} {K : ℕ} [NeZero K] (Pi : Finset (X → Fin K))
    (hPi : Pi.Nonempty) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (τ : ℕ → ℕ) (hτ0 : τ 0 = 0) (hτ : StrictMono τ)
    (hτ2 : ∀ m, 1 ≤ m → τ (m + 1) ≤ 2 * τ m) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, muM Pi δ τ (epochOf τ t - 1) ≤
      (τ (m0 Pi δ τ) : ℝ) / (2 * (K : ℝ))
        + Real.sqrt (8 * dT Pi δ (τ (epochOf τ T)) * (τ (epochOf τ T) : ℝ) / (K : ℝ)) := by sorry

end TamingMonster.Regret
