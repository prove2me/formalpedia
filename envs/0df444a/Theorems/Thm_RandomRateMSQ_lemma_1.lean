-- Prove2me | Theorems.Thm_RandomRateMSQ_lemma_1
-- name    : RandomRateMSQ.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:28:08.544062+00:00
-- url     : https://prove2.me/theorems/798c4813-76f4-45db-a80b-ff0749619220
-- title:
--   Lemma 1 — tightness of the maximal scaled idleness $|\hat I^n|_{*,T}$
-- statement:
--   Let the systems $n=0,1,2,\dots$ satisfy the model (any non-idling, non-anticipating, non-preemptive routing) and Assumptions 1 and 2. For every $T>0$ the maximal scaled idleness $|\hat I^n|_{*,T}=\sup_{0\le t\le T}|\hat I^n(t)|$ is tight: for every $\varepsilon>0$ there is $K$ with
--
--   $$
--   P\big(|\hat I^n|_{*,T}>K\big)<\varepsilon\qquad\text{for all }n .
--   $$
--
--   The total number of idle servers is therefore of order $\sqrt n$, which is what makes the fairness process and the diffusion scaling consistent.
--
--   Differences from the source:
--   - encoding: sup_{0≤t≤T} of a real process → supremum of ENNReal.ofReal |·| over t ≤ T, in [0, ∞]; reason: no junk value for unbounded sets; the probabilities are the printed ones
--   - reading: non-anticipating routing: the server is chosen based on the information available so far (p.5) → a filtration G containing the system's past, with the potential completions and the abandonment clock after t independent of G_t (the latter again unit Poisson) and the interarrival times after the one in progress independent of G_t; reason: the page gives a one-line description; this is the standard formalization, it admits every routing rule that uses the past and independent randomization, and it assumes no consequence (the service martingale is proved, not assumed)
--   - generalization: exponential patience with rate γ (γ > 0) → γ ≥ 0; reason: γ = 0 is the model without abandonment (Atar's setting); γ enters the proof only through M̂ⁿ₂ and a Lipschitz drift; the statement specializes to γ > 0
--   - reading: interarrival times uⁿᵢ i.i.d. with mean 1 (p.5) → law F_u with mean 1 and finite second moment; reason: the page's model presupposes it: var(uⁿₖ) enters Theorem 5 through c²_a (p.17), and the proofs apply the functional central limit theorem for renewal processes (pp.7, 8, 18), which needs a finite variance
--   - encoding: n-th system with servers k = 1..n, renewal arrivals and Poisson processes, time t ≥ 0, each system on its own space → time ℝ≥0, servers Fin n, families indexed by ℕ and used from 1, unit Poisson processes given by i.i.d. exponential(1) gaps, counts converted from ℕ∞ to ℕ (finite almost surely), interarrival times ≥ 0 and λₙ > 0, all systems on one probability space, the system equations required almost surely; reason: Lean conventions; every instance of the source's model is an instance of IsModelSeq (systems on separate spaces can be placed on their product) and conversely; only laws enter the statements
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, Lemma 1, p.7 (tightness as in its proof, p.7)

import Mathlib
import Definitions.Def_RandomRateMSQ_IsModel
import Definitions.Def_RandomRateMSQ_fairness

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace RandomRateMSQ

/-- **Lemma 1** (Büke–Qin, arXiv:1905.04198v1, p.7): "For any fixed T > 0 and nonidling policy,
{|Îⁿ|∗,T}_{n∈ℕ} is tight", i.e. (proof, p.7) for every `ε > 0` there is `K` with
`P(sup_{0≤t≤T} |Îⁿ(t)| > K) < ε` for all `n`. Stated for every sequence of systems satisfying the
model (non-idling, non-anticipating, non-preemptive routing) and Assumptions 1 and 2.

**Formalization Note.** The supremum is taken in `[0, ∞]`. -/
theorem lemma_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fu : Measure ℝ) (F : Measure ℝ≥0) (lam : ℕ → ℝ) (lamHat γ : ℝ)
    (G : ℕ → Filtration ℝ≥0 mΩ) (sys : ∀ n, System Ω n)
    (hmodel : IsModelSeq P Fu F lam γ G sys) (hA1 : Assumption1 F lam lamHat)
    (hA2 : Assumption2 P sys) (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, ∀ n, P {ω | ENNReal.ofReal K <
      ⨆ (t : ℝ≥0) (_ : t ≤ T), ENNReal.ofReal |Ihat (sys n) ω t|} < ENNReal.ofReal ε := by sorry

end RandomRateMSQ
