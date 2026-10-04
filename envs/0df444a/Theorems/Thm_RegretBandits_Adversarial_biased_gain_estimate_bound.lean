-- Prove2me | Theorems.Thm_RegretBandits_Adversarial_biased_gain_estimate_bound
-- name    : RegretBandits.Adversarial.biased_gain_estimate_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:32:12.851917+00:00
-- url     : https://prove2.me/theorems/2ca2662c-03f0-4273-a2e1-4bb9d692f45c
-- title:
--   Lemma 3.1 — high-probability bound for the biased gain estimates
-- statement:
--   Consider the adversarial bandit protocol with $K \ge 2$ arms and an adaptive adversary with gains $g_{i,t} \in [0,1]$, and let $I_1, I_2, \dots$ be a run of a forecaster that draws $I_t$ from the probability vector $p_t$, a function of $I_1,\dots,I_{t-1}$. Fix an arm $i$ with $p_{i,t} > 0$ for every round and every history, a horizon $n$, $\beta \in (0,1]$ and $\delta \in (0,1)$, and let
--   $$
--   \tilde g_{i,t} = \frac{g_{i,t} \mathbb 1_{I_t = i} + \beta}{p_{i,t}}.
--   $$
--   Then, with probability at least $1 - \delta$,
--   $$
--   \sum_{t=1}^n g_{i,t} \le \sum_{t=1}^n \tilde g_{i,t} + \frac{\ln(\delta^{-1})}{\beta}.
--   $$
--
--   The lemma says that the biased estimate $\tilde G_{i,n}$ used by Exp3.P overestimates the true cumulative gain only by an additive $\ln(\delta^{-1})/\beta$ with high probability; it is the concentration step in the proof of Theorem 3.2.
--
--   **Formalization Note** The book states the lemma for the distributions $p_{i,t}$ of Exp3.P with the single hypothesis $\beta \le 1$. The statement here holds for any forecaster rule (the book's proof uses only that $g_{i,t}$ and $p_{i,t}$ are determined by $I_1,\dots,I_{t-1}$ and that $I_t \sim p_t$ given the past), which contains Exp3.P. It adds the hypotheses implicit on the page: $\beta > 0$ (the bound divides by $\beta$), $p_{i,t} > 0$ (the estimate divides by $p_{i,t}$; Exp3.P has $p_{i,t} \ge \gamma/K$ and positive exponential weights), $\delta \in (0,1)$, and the standing $K \ge 2$ of the protocol (p. 6). "With probability at least $1-\delta$" is $\mathbb P(\text{event}) \ge 1-\delta$ under the law of the run.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 28, Lemma 3.1

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_Protocol

open MeasureTheory

namespace RegretBandits.Adversarial

/-- Lemma 3.1 (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 28). Let `p` be a forecaster rule run
against an adaptive adversary `g` with gains in `[0,1]`, fix an arm `i` with `p_{i,t} > 0`, and
let `0 < β ≤ 1`, `δ ∈ (0,1)`. With `g̃_{i,t} = (g_{i,t} 𝟙{I_t = i} + β) / p_{i,t}`, with probability
at least `1 - δ`,
`∑_{t=1}^n g_{i,t} ≤ ∑_{t=1}^n g̃_{i,t} + ln(δ⁻¹) / β`. -/
theorem biased_gain_estimate_bound {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (g : Adversary K)
    (p : ℕ → (ℕ → Fin K) → Fin K → ℝ) (hp : IsForecasterRule p) (i : Fin K)
    (hpos : ∀ t h, 0 < p t h i) (β δ : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (I : ℕ → Ω → Fin K) (hI : IsRun P p I) :
    ENNReal.ofReal (1 - δ) ≤
      P {ω | ∑ t ∈ Finset.Icc 1 n, g.val t (fun s => I s ω) i ≤
        ∑ t ∈ Finset.Icc 1 n,
            (g.val t (fun s => I s ω) i * (if I t ω = i then 1 else 0) + β) /
              p t (fun s => I s ω) i +
          Real.log δ⁻¹ / β} := by sorry

end RegretBandits.Adversarial
