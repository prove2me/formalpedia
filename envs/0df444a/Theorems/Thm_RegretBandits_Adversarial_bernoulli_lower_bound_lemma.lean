-- Prove2me | Theorems.Thm_RegretBandits_Adversarial_bernoulli_lower_bound_lemma
-- name    : RegretBandits.Adversarial.bernoulli_lower_bound_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:33:09.126225+00:00
-- url     : https://prove2.me/theorems/4a69ac13-5201-41b1-8258-08bb88e5cc5c
-- title:
--   Lemma 3.2 — regret lower bound on ε-perturbed Bernoulli instances
-- statement:
--   Let $K \ge 2$, $n \in \mathbb N$ and $\varepsilon \in [0,1)$. For each arm $i \in \{1,\dots,K\}$, consider the stochastic instance in which all arms give i.i.d. Bernoulli rewards with parameter $\frac{1-\varepsilon}{2}$, except arm $i$, whose rewards are i.i.d. Bernoulli with parameter $\frac{1+\varepsilon}{2}$, and let $\mathbb E_i$ be the expectation when a given forecaster plays on that instance. Then, for any forecaster,
--   $$
--   \max_{i=1,\dots,K} \mathbb E_i \sum_{t=1}^n \bigl(Y_{i,t} - Y_{I_t,t}\bigr) \ge n\varepsilon\left(1 - \frac1K - \sqrt{\varepsilon\ln\frac{1+\varepsilon}{1-\varepsilon}}\sqrt{\frac{n}{2K}}\right).
--   $$
--
--   The lemma is the general engine of the minimax lower bound (Theorem 3.4), which follows by choosing $\varepsilon$ of order $\sqrt{K/n}$.
--
--   **Formalization Note** "For any forecaster" quantifies over all forecaster rules that map the observed past (actions and the rewards of the played arms) to a distribution on the arms; this covers deterministic and randomized forecasters. For each $i$ the expectation $\mathbb E_i$ is taken under any run of the forecaster on instance $i$; the law of the run, and hence $\mathbb E_i$, is determined by the forecaster and the instance. The standing $K \ge 2$ of the protocol (p. 6) is added.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 34, Lemma 3.2

import Mathlib
import Definitions.Def_RegretBandits_Adversarial_BernoulliModel

open MeasureTheory

namespace RegretBandits.Adversarial

/-- Lemma 3.2 (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 34). Let `ε ∈ [0,1)` and let `q` be any
forecaster. For each arm `i`, let `(I^{(i)}, Y^{(i)})` be a run of `q` on the instance where all arms
are i.i.d. Bernoulli`((1-ε)/2)` except arm `i`, which is i.i.d. Bernoulli`((1+ε)/2)`, and let `E_i`
be the expectation under `P_i`. Then
`max_i E_i ∑_{t=1}^n (Y_{i,t} - Y_{I_t,t}) ≥ n ε (1 - 1/K - √(ε ln((1+ε)/(1-ε))) √(n/(2K)))`. -/
theorem bernoulli_lower_bound_lemma {K : ℕ} (hK : 2 ≤ K) (n : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) (q : ℕ → (ℕ → Fin K) → (ℕ → Bool) → Fin K → ℝ) (hq : IsBanditForecaster q)
    {Ω : Type*} [MeasurableSpace Ω] (P : Fin K → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (I : Fin K → ℕ → Ω → Fin K) (Y : Fin K → ℕ → Ω → Fin K → Bool)
    (hrun : ∀ i, IsBernoulliRun (P i) (epsInstance ε i) q (I i) (Y i)) :
    n * ε * (1 - 1 / K - Real.sqrt (ε * Real.log ((1 + ε) / (1 - ε))) * Real.sqrt (n / (2 * K)))
      ≤ ⨆ i : Fin K, ∫ ω, ∑ t ∈ Finset.Icc 1 n,
          (rewardVal (Y i t ω i) - rewardVal (Y i t ω (I i t ω))) ∂(P i) := by sorry

end RegretBandits.Adversarial
