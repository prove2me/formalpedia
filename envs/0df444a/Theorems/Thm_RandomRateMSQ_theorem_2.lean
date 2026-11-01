-- Prove2me | Theorems.Thm_RandomRateMSQ_theorem_2
-- name    : RandomRateMSQ.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:28:07.912131+00:00
-- url     : https://prove2.me/theorems/7b16c96a-5603-43f5-9d0b-ccf1f5e41891
-- title:
--   Theorem 2 — tightness of the $\varepsilon$-shifted fairness processes $\{S^n_\varepsilon\eta^n\}$
-- statement:
--   Under the model and Assumptions 1, 2 and 3, for every $\varepsilon>0$ the sequence of $\varepsilon$-shifted fairness processes $\{S^n_\varepsilon\eta^n\}_{n}$ is tight in $G_{\mathcal P}[0,\infty)$ with the Skorokhod $J_1$ topology: every subsequence has a further subsequence converging in distribution.
--
--   The unshifted fairness processes are not tight in any of Skorokhod's topologies (Remark 1); the shift removes the oscillation near $\tau^n_0$, and this tightness is what Definition 1's notion of a limiting fairness process rests on.
--
--   Differences from the source:
--   - reading: G_P[0, ∞) with Skorokhod J1 defined by time reversal on [a, b] and extended to [0, ∞) 'in a similar manner' (p.3) → J1 for left-continuous paths via time changes of [0, ∞), uniform on compacts, Lévy–Prokhorov distance on P; reason: the printed definition is garbled (the domains do not match); on each [0, T] time changes commute with time reversal, and the global form is the standard extension (Whitt; public J1Tendsto)
--   - encoding: weak convergence of laws (⇒) → coupling form: copies on one probability space converging almost surely; reason: equivalent by the Skorokhod representation theorem on Polish spaces; the form of public PuhaWardFluid.Limit.ConvInDist
--   - reading: non-anticipating routing: the server is chosen based on the information available so far (p.5) → a filtration G containing the system's past, with the potential completions and the abandonment clock after t independent of G_t (the latter again unit Poisson) and the interarrival times after the one in progress independent of G_t; reason: the page gives a one-line description; this is the standard formalization, it admits every routing rule that uses the past and independent randomization, and it assumes no consequence (the service martingale is proved, not assumed)
--   - generalization: exponential patience with rate γ (γ > 0) → γ ≥ 0; reason: γ = 0 is the model without abandonment (Atar's setting); γ enters the proof only through M̂ⁿ₂ and a Lipschitz drift; the statement specializes to γ > 0
--   - reading: interarrival times uⁿᵢ i.i.d. with mean 1 (p.5) → law F_u with mean 1 and finite second moment; reason: the page's model presupposes it: var(uⁿₖ) enters Theorem 5 through c²_a (p.17), and the proofs apply the functional central limit theorem for renewal processes (pp.7, 8, 18), which needs a finite variance
--   - encoding: n-th system with servers k = 1..n, renewal arrivals and Poisson processes, time t ≥ 0, each system on its own space → time ℝ≥0, servers Fin n, families indexed by ℕ and used from 1, unit Poisson processes given by i.i.d. exponential(1) gaps, counts converted from ℕ∞ to ℕ (finite almost surely), interarrival times ≥ 0 and λₙ > 0, all systems on one probability space, the system equations required almost surely; reason: Lean conventions; every instance of the source's model is an instance of IsModelSeq (systems on separate spaces can be placed on their product) and conversely; only laws enter the statements
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, Theorem 2, p.11

import Mathlib
import Definitions.Def_RandomRateMSQ_IsModel
import Definitions.Def_RandomRateMSQ_fairness

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace RandomRateMSQ

/-- **Theorem 2** (Büke–Qin, arXiv:1905.04198v1, p.11): "For any ε > 0, the sequence of ε-shifted
processes {Sⁿ_ε ηⁿ}_{n∈ℕ} is tight", on `G_P[0, ∞)` with the Skorokhod `J₁` topology, under the
model and Assumptions 1, 2 and 3.

**Formalization Note.** Tightness is relative compactness in distribution
(`RelCompactInDistLeft`: every subsequence has a further subsequence converging in distribution,
coupling form) for left-continuous `J₁` with the Lévy–Prokhorov distance on `P`; by Prokhorov's
theorem this is tightness on a Polish path space. -/
theorem theorem_2 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fu : Measure ℝ) (F : Measure ℝ≥0) (lam : ℕ → ℝ) (lamHat γ : ℝ)
    (G : ℕ → Filtration ℝ≥0 mΩ) (sys : ∀ n, System Ω n)
    (hmodel : IsModelSeq P Fu F lam γ G sys) (hA1 : Assumption1 F lam lamHat)
    (hA2 : Assumption2 P sys) (ζ : ProbabilityMeasure ℝ≥0) (hA3 : Assumption3 P ζ sys)
    (ε : ℝ) (hε : 0 < ε) :
    RelCompactInDistLeft lpDist P (fun n => shiftedFairness ζ (sys n) ε) := by sorry

end RandomRateMSQ
