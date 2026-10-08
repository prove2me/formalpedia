-- Prove2me | Theorems.Thm_TDApprox_Conv_theorem_1
-- name    : TDApprox.Conv.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:17.724034+00:00
-- url     : https://prove2.me/theorems/2a9f4f68-8908-434c-87b2-d312623ed86f
-- title:
--   Theorem 1, p. 11 — J* ∈ L₂(S, D); TD(λ) converges w.p. 1 to the unique r* with ΠT^(λ)(Φ′r*) = Φ′r*; ‖Φ′r* − J*‖_D ≤ ‖ΠJ* − J*‖_D/(1 − α(1−λ)/(1−λα))
-- statement:
--   Consider a Markov chain on a finite or countably infinite state space $S$ with transition matrix $P$, transition costs $g(i,j)$ and discount factor $\alpha \in (0,1)$, with cost-to-go
--   $$J^*(i) = E\Big[\sum_{t=0}^\infty \alpha^t g(i_t,i_{t+1}) \,\Big|\, i_0 = i\Big].$$
--   Approximate $J^*$ by $\Phi'r$, where $\phi_1,\dots,\phi_K$ are basis functions. TD($\lambda$) starts from an arbitrary $r_0$ and observes the chain $i_0, i_1, \dots$. With eligibility vectors $z_t = \sum_{k=0}^t(\alpha\lambda)^{t-k}\phi(i_k)$ and temporal differences $d_t = g(i_t,i_{t+1}) + \alpha\phi(i_{t+1})'r_t - \phi(i_t)'r_t$, it updates
--   $$r_{t+1} = r_t + \gamma_t d_t z_t.$$
--
--   Under Assumptions 1, 2, 3 and 4 (ergodicity with a positive invariant distribution $\pi$ and finite cost moments; linearly independent, square-integrable basis functions; polynomial growth and mixing conditions relative to state coordinates $\sigma(i) \in \mathbb R^N$; standard step sizes), the following hold:
--   1. (a) $J^* \in L_2(S,D)$;
--   2. (b) for any $\lambda \in [0,1]$, TD($\lambda$) converges with probability 1, from every initial state $i_0$ and every initial vector $r_0$;
--   3. (c) the limit $r^*$ is the unique solution of $\Pi T^{(\lambda)}(\Phi'r^*) = \Phi'r^*$;
--   4. (d) $r^*$ satisfies
--   $$\|\Phi'r^* - J^*\|_D \le \frac{\|\Pi J^* - J^*\|_D}{1 - \alpha(1-\lambda)/(1-\lambda\alpha)}.$$
--
--   This is the main result of the paper. It gives almost-sure convergence of on-line TD($\lambda$) with linear function approximation on possibly infinite state spaces, characterizes the limit as the fixed point of the projected operator $\Pi T^{(\lambda)}$, and bounds its error relative to the best approximation $\Pi J^*$.
--
--   **Formalization Note.** The objects and the four assumptions are those of the definitions file `TDApprox.Conv.Model`. Convergence is almost sure under the path law of the chain started at $i_0$, for every $i_0$ and $r_0$; the limit $r^*$ does not depend on them. Uniqueness in (c) is the equivalence $\Pi T^{(\lambda)}(\Phi'r) = \Phi'r \iff r = r^*$. The denominator of (d) is kept in the page's form; it equals $1$ at $\lambda = 1$ and is positive for $\lambda \in [0,1]$ because $\alpha < 1$.
-- source:
--   Tsitsiklis & Van Roy, LIDS-P-2322 (1996), Theorem 1, p. 11

import Mathlib
import Definitions.Def_TDApprox_Conv_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset Matrix

namespace TDApprox.Conv

/-- **Theorem 1** (Tsitsiklis & Van Roy, LIDS-P-2322 (1996), p. 11). Under Assumptions 1, 2, 3
and 4:
(a) the cost-to-go function `J*` is in `L₂(S, D)`;
(b) for any `λ ∈ [0, 1]`, the TD(λ) iterates converge with probability 1 (from every initial
state `i_0` and every initial vector `r_0`);
(c) the limit `r*` is the unique solution of `ΠT^(λ)(Φ′r*) = Φ′r*`;
(d) `‖Φ′r* − J*‖_D ≤ ‖ΠJ* − J*‖_D / (1 − α(1 − λ)/(1 − λα))`. -/
theorem theorem_1 {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (P : Kernel S S) [IsMarkovKernel P] (π : Measure S) [IsProbabilityMeasure π]
    (g : S → S → ℝ) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    {K : ℕ} (φ : S → Fin K → ℝ) {N : ℕ} (σ : S → Fin N → ℝ) (γ : ℕ → ℝ)
    (h1 : Assumption1 P π g α) (h2 : Assumption2 π φ) (h3 : Assumption3 P π g φ σ)
    (h4 : Assumption4 γ) :
    MemL2D π (Jstar P g α) ∧
    ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∃ rstar : Fin K → ℝ,
      (∀ (i₀ : S) (r₀ : Fin K → ℝ), ∀ᵐ ω ∂(pathLaw P i₀),
        Tendsto (fun t => tdIter α lam γ g φ r₀ ω t) atTop (𝓝 rstar)) ∧
      (∀ r : Fin K → ℝ,
        proj π φ (Tlam P g α lam (Jtilde φ r)) = Jtilde φ r ↔ r = rstar) ∧
      normD π (Jtilde φ rstar - Jstar P g α) ≤
        normD π (proj π φ (Jstar P g α) - Jstar P g α) / (1 - α * (1 - lam) / (1 - lam * α)) := by sorry

end TDApprox.Conv
