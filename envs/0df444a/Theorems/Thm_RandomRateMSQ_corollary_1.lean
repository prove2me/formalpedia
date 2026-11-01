-- Prove2me | Theorems.Thm_RandomRateMSQ_corollary_1
-- name    : RandomRateMSQ.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:28:02.452702+00:00
-- url     : https://prove2.me/theorems/deaf733f-f8d5-45d3-8a86-7bca671d1f92
-- title:
--   Corollary 1 — $|\bar I^n|_{*,T}\to0$ and $|\int_0^t(X^n-n)^+/n|_{*,T}\to0$ in probability
-- statement:
--   Under the model and Assumptions 1 and 2, for every $T>0$,
--
--   $$
--   |\bar I^n|_{*,T}\xrightarrow{\ p\ }0\qquad\text{and}\qquad\Big|\frac{\int_0^t(X^n(s)-n)^+ds}{n}\Big|_{*,T}\xrightarrow{\ p\ }0,
--   $$
--
--   where $\bar I^n=\sum_kI^n_k/n$ is the fraction of idle servers and $|f|_{*,T}=\sup_{0\le t\le T}|f(t)|$; convergence in probability means $P(|\cdot|_{*,T}>\delta)\to0$ for every $\delta>0$.
--
--   Both limits feed the computation of the quadratic variations of the service and abandonment martingales.
--
--   Differences from the source:
--   - encoding: sup_{0≤t≤T} of a real process → supremum of ENNReal.ofReal |·| over t ≤ T, in [0, ∞]; reason: no junk value for unbounded sets; the probabilities are the printed ones
--   - reading: non-anticipating routing: the server is chosen based on the information available so far (p.5) → a filtration G containing the system's past, with the potential completions and the abandonment clock after t independent of G_t (the latter again unit Poisson) and the interarrival times after the one in progress independent of G_t; reason: the page gives a one-line description; this is the standard formalization, it admits every routing rule that uses the past and independent randomization, and it assumes no consequence (the service martingale is proved, not assumed)
--   - generalization: exponential patience with rate γ (γ > 0) → γ ≥ 0; reason: γ = 0 is the model without abandonment (Atar's setting); γ enters the proof only through M̂ⁿ₂ and a Lipschitz drift; the statement specializes to γ > 0
--   - reading: interarrival times uⁿᵢ i.i.d. with mean 1 (p.5) → law F_u with mean 1 and finite second moment; reason: the page's model presupposes it: var(uⁿₖ) enters Theorem 5 through c²_a (p.17), and the proofs apply the functional central limit theorem for renewal processes (pp.7, 8, 18), which needs a finite variance
--   - encoding: n-th system with servers k = 1..n, renewal arrivals and Poisson processes, time t ≥ 0, each system on its own space → time ℝ≥0, servers Fin n, families indexed by ℕ and used from 1, unit Poisson processes given by i.i.d. exponential(1) gaps, counts converted from ℕ∞ to ℕ (finite almost surely), interarrival times ≥ 0 and λₙ > 0, all systems on one probability space, the system equations required almost surely; reason: Lean conventions; every instance of the source's model is an instance of IsModelSeq (systems on separate spaces can be placed on their product) and conversely; only laws enter the statements
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, Corollary 1, p.8

import Mathlib
import Definitions.Def_RandomRateMSQ_IsModel
import Definitions.Def_RandomRateMSQ_fairness

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace RandomRateMSQ

/-- **Corollary 1** (Büke–Qin, arXiv:1905.04198v1, p.8): "|Īⁿ|∗,T →p 0 and
|∫₀ᵗ (Xⁿ(s) − n)⁺ ds / n|∗,T →p 0", for every `T > 0`, under the model and Assumptions 1 and 2
(those of Lemma 1). Here `Īⁿ = Σₖ Iⁿₖ/n` and `|f|∗,T = sup_{0≤t≤T} |f(t)|` (p.3).

**Formalization Note.** Convergence in probability to `0`: `P(|·|∗,T > δ) → 0` for every `δ > 0`;
the supremum is taken in `[0, ∞]`. -/
theorem corollary_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fu : Measure ℝ) (F : Measure ℝ≥0) (lam : ℕ → ℝ) (lamHat γ : ℝ)
    (G : ℕ → Filtration ℝ≥0 mΩ) (sys : ∀ n, System Ω n)
    (hmodel : IsModelSeq P Fu F lam γ G sys) (hA1 : Assumption1 F lam lamHat)
    (hA2 : Assumption2 P sys) (T : ℝ≥0) (hT : 0 < T) :
    (∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | ENNReal.ofReal δ <
      ⨆ (t : ℝ≥0) (_ : t ≤ T), ENNReal.ofReal |Ibar (sys n) ω t|}) atTop (𝓝 0)) ∧
    (∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | ENNReal.ofReal δ <
      ⨆ (t : ℝ≥0) (_ : t ≤ T), ENNReal.ofReal |(sys n).cumOverflow ω t / n|}) atTop (𝓝 0)) := by sorry

end RandomRateMSQ
