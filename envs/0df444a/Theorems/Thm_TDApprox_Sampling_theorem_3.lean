-- Prove2me | Theorems.Thm_TDApprox_Sampling_theorem_3
-- name    : TDApprox.Sampling.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:49.765286+00:00
-- url     : https://prove2.me/theorems/2316e9eb-6b4c-45fc-8cd6-6e52c2cee291
-- title:
--   Theorem 3, p. 24 — q-sampled TD(0) can diverge in expectation
-- statement:
--   Let $S$ be a finite or countably infinite state space with at least two states, let $q$ be any probability distribution on $S$, choose $5/6<\alpha<1$, and let $\gamma_t$ satisfy Assumption 4. There exist a Markov transition matrix $P$, a transition cost function $g$, an invariant distribution $\pi$, and a feature map $\phi$ with $K\ge1$ linearly independent basis functions, satisfying Assumptions 1 and 2. For the unique parameter $r^*$ solving the projected TD(0) fixed-point equation, every other deterministic initialization and every realization of the specified independent $q$-sampled process satisfy
--
--   $$\Pi T^{(0)}(\phi^{\mathsf T}r)=\phi^{\mathsf T}r\iff r=r^*,\qquad \lim_{t\to\infty}\lVert\mathbb E[r_t\mid r_0]\rVert=\infty\quad(r_0\ne r^*).$$
--
--   This counterexample shows that sampling states independently according to an arbitrary distribution can destroy the convergence behavior established for on-line sampling under the chain's invariant law.
--
--   **Formalization Note** The source's $|S|\ge2$ is a nontrivial countable type. The number $K$ of basis functions is existential, as is the page's matrix $\Phi$; the witness must have $K\ge1$, because with $K=0$ the parameter space $\mathbb R^0$ is a single point and the conclusion would hold vacuously (the paper's construction has $K=1$). The fixed-point equation identifies $r^*$, and the conclusion includes integrability of each finite-time parameter vector. The expectation is over the sampled process with $r_0$ fixed. The quantified probability spaces have type universe zero.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Theorem 3, p. 24; https://dspace.mit.edu/entities/publication/ab395d25-a6d3-407a-9589-60eaac58fd05

import Mathlib
import Definitions.Def_TDApprox_Sampling_Model

namespace TDApprox.Sampling

open MeasureTheory ProbabilityTheory Filter

theorem theorem_3
    {S : Type} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    [Nontrivial S] (q : S → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq : HasSum q 1)
    (α : ℝ) (hα₁ : (5 : ℝ) / 6 < α) (hα₂ : α < 1)
    (γ : ℕ → ℝ) (hγ : TDApprox.Conv.Assumption4 γ) :
    ∃ P : Kernel S S, ∃ hP : IsMarkovKernel P,
    letI : IsMarkovKernel P := hP
    ∃ π : Measure S, ∃ hπ : IsProbabilityMeasure π,
    letI : IsProbabilityMeasure π := hπ
    ∃ g : S → S → ℝ, ∃ K : ℕ, 0 < K ∧ ∃ φ : S → Fin K → ℝ,
      Assumption1 P π g α ∧ Assumption2 π φ ∧
      ∃ rstar : Fin K → ℝ,
        (∀ r : Fin K → ℝ,
          proj π φ (T0 P g α (fun i => dotProduct (φ i) r)) =
            (fun i => dotProduct (φ i) r) ↔ r = rstar) ∧
        ∀ r₀ : Fin K → ℝ, r₀ ≠ rstar →
          ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
            (I J : ℕ → Ω → S), IsQSample μ q P I J →
              (∀ t, Integrable (fun ω => qIter α γ g φ r₀ I J t ω) μ) ∧
              Tendsto (fun t => ‖∫ ω, qIter α γ g φ r₀ I J t ω ∂μ‖)
                atTop atTop := by sorry

end TDApprox.Sampling
