-- Prove2me | Theorems.Thm_StrictCompatLB_MeanField_meanfield_limit_and_steady_state
-- name    : StrictCompatLB.MeanField.meanfield_limit_and_steady_state
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:51:43.378901+00:00
-- url     : https://prove2.me/theorems/77ae612d-3b01-4a57-8b53-6152bd73b514
-- title:
--   Theorem 3.4 — on proportionally sparse (and subcritical) compatibility graphs, JSQ(d) has the fully flexible mean-field limit and steady state
-- statement:
--   Let $0<\lambda<1$ and $d\ge2$. Tasks arrive at $M(N)$ dispatchers as independent Poisson streams of rate $\lambda N/M(N)$; a task arriving at dispatcher $w$ samples $\min(d,|\mathcal N_w|)$ servers of its neighbourhood $\mathcal N_w$ uniformly at random without replacement and joins a shortest of their queues (ties broken uniformly); services are exponential with unit mean. Let $\{G_N\}_{N\ge1}$ be a proportionally sparse sequence of connected compatibility graphs, and $\Phi(G_N,t)$ the vector of queue lengths at time $t$.
--
--   1. **Process level.** Suppose $q^*(0)\in\mathcal Y$ and $\|q(\Phi(G_N,0))-q^*(0)\|_1\to0$, and let $q^*$ be the $\mathcal Y$-valued solution of
--   $$\frac{dq^*_i(t)}{dt}=\lambda\big(q^*_{i-1}(t)^d-q^*_i(t)^d\big)-\big(q^*_i(t)-q^*_{i+1}(t)\big),\qquad i=1,2,\dots\qquad(3.3)$$
--   with this initial value. Then for every $T\ge0$ and $\varepsilon>0$,
--   $$P\Big(\sup_{t\in[0,T]}\|q(\Phi(G_N,t))-q^*(t)\|_1\ge\varepsilon\Big)\longrightarrow0\qquad(N\to\infty).$$
--   2. **Steady state.** If moreover $\{G_N\}$ satisfies the subcriticality condition, there is $N_0$ such that for every $N\ge N_0$ the process $\Phi(G_N,\cdot)$ has a unique stationary distribution $\pi_N$, and $q(\Phi(G_N,\infty))$ converges to the fixed point
--   $$q^*_i(\infty)=\lambda^{\frac{d^i-1}{d-1}},\qquad i=1,2,\dots,$$
--   in the sense that $\pi_N\big(\|q-q^*(\infty)\|_1\ge\varepsilon\big)\to0$ for every $\varepsilon>0$.
--
--   Thus a sparse compatibility graph, as long as it is proportionally sparse and subcritical, gives the same transient and stationary mean-field behaviour as the fully flexible system, where every task may join every server.
--
--   **Formalization Note** Two printed defects are repaired. (i) The printed (3.4) reads $\lambda^{(d^i-d)/(d-1)}$, which gives $q^*_1(\infty)=1$ and is not the fixed point of (3.3); the statement uses $\lambda^{(d^i-1)/(d-1)}$ (`PowerTwoChoices.Limit.fixedPoint`). (ii) "For each fixed $N$, the Markov process is ergodic" is asserted for all $N\ge N_0$, as Theorem 4.8(i) proves; for small $N$ it can fail. Weak convergence in Skorohod $J_1$ to a continuous deterministic path, and weak convergence to a constant, are rendered as convergence in probability. Ergodicity is rendered as existence and uniqueness of a stationary distribution of the uniformised chain. The process is any realisation, for $N\ge1$, of the uniformised chain (`IsLBProcess` with `jsqdRoute`); the solution of (3.3) is any $\mathcal Y$-valued `IsTrajectory`. Both quantifications are over nonempty classes: the chain can be realised by Ionescu-Tulcea with an independent i.i.d. exponential clock, and (3.3) has a $\mathcal Y$-valued solution from every point of $\mathcal Y$. $\|\cdot\|_1$ is `l1dist`, which includes coordinate $0$, equal to $1$ on both sides.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 12, Theorem 3.4, (3.3), (3.4); pp. 8–9, §2 (model)

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model

open Filter Topology MeasureTheory
open scoped ENNReal

namespace StrictCompatLB.MeanField

/-- Theorem 3.4 (p. 12), with the fixed point (3.4) corrected to `q*_i(∞) = λ^{(d^i−1)/(d−1)}` and
ergodicity asserted for all large `N`. Let `0 < λ < 1`, `d ≥ 2`, and let `{G_N}` be a
proportionally sparse sequence of connected graphs.
1. (Process level.) If `q*(0) ∈ 𝒴` and `‖q(Φ(G_N, 0)) − q*(0)‖₁ → 0`, then for every `𝒴`-valued
   solution `q*` of (3.3) with this initial value, every `T ≥ 0` and `ε > 0`,
   `P(sup_{t ∈ [0,T]} ‖q(Φ(G_N, t)) − q*(t)‖₁ ≥ ε) → 0` under JSQ(d).
2. (Steady state.) If moreover `{G_N}` satisfies the subcriticality condition, then there is
   `N₀` such that the JSQ(d) chain on `G_N` has a unique stationary distribution `π_N` for
   every `N ≥ N₀`, and `π_N(‖q − q*(∞)‖₁ ≥ ε) → 0` for every `ε > 0`. -/
theorem meanfield_limit_and_steady_state (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (d : ℕ) (hd : 2 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsparse : IsPropSparse M G) :
    (∀ (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ), InY q₀ →
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
      ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
        (∀ t : ℝ, 0 ≤ t → InY (s t)) → s 0 = q₀ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
          (∀ N, 1 ≤ N → IsLBProcess P lam M N (jsqdRoute M G N d) (z₀ N) (Y N) (τ N)) →
          ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
              atTop (𝓝 0)) ∧
    (IsSubcritical d M G →
      ∃ N₀ : ℕ, (∀ N ≥ N₀, ∃! π : (Fin N → ℕ) → ℝ, IsStationary (jsqdKernel lam d M G N) π) ∧
        ∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N) {z | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.l1dist (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)})
              atTop (𝓝 0)) := by sorry

end StrictCompatLB.MeanField
