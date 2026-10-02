-- Prove2me | Theorems.Thm_TamingMonster_Regret_sum_mu_le
-- name    : TamingMonster.Regret.sum_mu_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T08:56:39.965308+00:00
-- url     : https://prove2.me/theorems/d3b81ef5-f2e9-44e1-8e84-52764d20a564
-- title:
--   Lemma 15 — $\sum_{t=1}^T\mu_{m(t)}\le2\sqrt{d_{\tau_{m(T)}}\tau_{m(T)}/K}$
-- statement:
--   Let $K\ge1$, $\Pi$ a finite nonempty policy class, $\delta\in(0,1)$, and $0=\tau_0<\tau_1<\cdots$ an epoch schedule, with $d_t=\ln(16t^2|\Pi|/\delta)$, $\mu_m=\min\{1/(2K),\sqrt{d_{\tau_m}/(K\tau_m)}\}$ and $m(t)=\min\{m:t\le\tau_m\}$. For every $T\in\mathbb N$,
--   $$\sum_{t=1}^T\mu_{m(t)}\le2\sqrt{\frac{d_{\tau_{m(T)}}\,\tau_{m(T)}}{K}}.$$
--
--   This deterministic summation bound converts per-round exploration levels into the $\sqrt{KT\ln(T|\Pi|/\delta)}$ term of the regret.
--
--   **Formalization Note** $T=0$ is allowed (both sides are $0$).
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 20, Lemma 15

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting
import Definitions.Def_TamingMonster_Regret_Algorithm
import Definitions.Def_TamingMonster_Regret_Analysis

namespace TamingMonster.Regret

open MeasureTheory

/-- Lemma 15, p. 20. For every `T`, `∑_{t=1}^T μ_{m(t)} ≤ 2√(d_{τ_{m(T)}} τ_{m(T)}/K)`. -/
theorem sum_mu_le {X : Type*} {K : ℕ} [NeZero K] (Pi : Finset (X → Fin K))
    (hPi : Pi.Nonempty) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (τ : ℕ → ℕ) (hτ0 : τ 0 = 0) (hτ : StrictMono τ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, muM Pi δ τ (epochOf τ t) ≤
      2 * Real.sqrt (dT Pi δ (τ (epochOf τ T)) * (τ (epochOf τ T) : ℝ) / (K : ℝ)) := by sorry

end TamingMonster.Regret
