-- Prove2me | Theorems.Thm_RandomRateMSQ_lemma_2
-- name    : RandomRateMSQ.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:28:13.172934+00:00
-- url     : https://prove2.me/theorems/75302872-bffe-43e4-be3b-fcc6aad8fe35
-- title:
--   Lemma 2 — $\sup_{t\le T}\sum_k\tilde\mu_k\int_0^tI_k/n\to0$ in probability
-- statement:
--   Under the model and Assumptions 1 and 2, for every $T\ge0$,
--
--   $$
--   \sup_{0\le t\le T}\frac{\sum_{k=1}^n\tilde\mu^n_k\int_0^tI^n_k(s)\,ds}{n}\xrightarrow{\ p\ }0 .
--   $$
--
--   The service capacity lost to idleness is negligible on the fluid scale, even though the rates are random and unbounded.
--
--   Differences from the source:
--   - encoding: sup_{0≤t≤T} of a real process → supremum of ENNReal.ofReal |·| over t ≤ T, in [0, ∞]; reason: no junk value for unbounded sets; the probabilities are the printed ones
--   - reading: non-anticipating routing: the server is chosen based on the information available so far (p.5) → a filtration G containing the system's past, with the potential completions and the abandonment clock after t independent of G_t (the latter again unit Poisson) and the interarrival times after the one in progress independent of G_t; reason: the page gives a one-line description; this is the standard formalization, it admits every routing rule that uses the past and independent randomization, and it assumes no consequence (the service martingale is proved, not assumed)
--   - generalization: exponential patience with rate γ (γ > 0) → γ ≥ 0; reason: γ = 0 is the model without abandonment (Atar's setting); γ enters the proof only through M̂ⁿ₂ and a Lipschitz drift; the statement specializes to γ > 0
--   - reading: interarrival times uⁿᵢ i.i.d. with mean 1 (p.5) → law F_u with mean 1 and finite second moment; reason: the page's model presupposes it: var(uⁿₖ) enters Theorem 5 through c²_a (p.17), and the proofs apply the functional central limit theorem for renewal processes (pp.7, 8, 18), which needs a finite variance
--   - encoding: n-th system with servers k = 1..n, renewal arrivals and Poisson processes, time t ≥ 0, each system on its own space → time ℝ≥0, servers Fin n, families indexed by ℕ and used from 1, unit Poisson processes given by i.i.d. exponential(1) gaps, counts converted from ℕ∞ to ℕ (finite almost surely), interarrival times ≥ 0 and λₙ > 0, all systems on one probability space, the system equations required almost surely; reason: Lean conventions; every instance of the source's model is an instance of IsModelSeq (systems on separate spaces can be placed on their product) and conversely; only laws enter the statements
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, Lemma 2, p.8

import Mathlib
import Definitions.Def_RandomRateMSQ_IsModel
import Definitions.Def_RandomRateMSQ_fairness

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace RandomRateMSQ

/-- **Lemma 2** (Büke–Qin, arXiv:1905.04198v1, p.8): "For any nonidling policy we have
sup_{0≤t≤T} Σ_{k=1}^{n} µₖ ∫₀ᵗ Iₖ(s) ds / n →p 0 for any given T", where `µₖ = µ̃ⁿₖ` are the
random rates; under the model and Assumptions 1 and 2 (the proof, p.9, rests on Lemma 1).

**Formalization Note.** Convergence in probability to `0` as in `corollary_1`. -/
theorem lemma_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fu : Measure ℝ) (F : Measure ℝ≥0) (lam : ℕ → ℝ) (lamHat γ : ℝ)
    (G : ℕ → Filtration ℝ≥0 mΩ) (sys : ∀ n, System Ω n)
    (hmodel : IsModelSeq P Fu F lam γ G sys) (hA1 : Assumption1 F lam lamHat)
    (hA2 : Assumption2 P sys) (T : ℝ≥0) :
    ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | ENNReal.ofReal δ <
      ⨆ (t : ℝ≥0) (_ : t ≤ T), ENNReal.ofReal
        |(∑ k, ((sys n).rate k ω : ℝ) * cumInt (fun r => ((sys n).I k ω r : ℝ)) t) / n|})
      atTop (𝓝 0) := by sorry

end RandomRateMSQ
