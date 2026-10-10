-- Prove2me | Theorems.Thm_PowerOfDUniversality_Diffusion_theorem_2_4
-- name    : PowerOfDUniversality.Diffusion.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:36:56.616042+00:00
-- url     : https://prove2.me/theorems/3dc98522-34f6-4fda-a618-a3d20cb00165
-- title:
--   Theorem 2.4 — universality of the Halfin–Whitt diffusion limit for JSQ(d(N)) when $d(N)/(\sqrt N\log N)\to\infty$
-- statement:
--   Consider $N$ parallel single-server queues with buffer size $b\ge2$ (possibly infinite), unit-mean exponential service, Poisson arrivals of rate $\lambda(N)$ and the JSQ(d(N)) dispatching scheme, in the Halfin–Whitt regime
--   $$\frac{N-\lambda(N)}{\sqrt N}\to\beta>0 .$$
--   Let $k\ge2$ and let $\nu$ be a probability measure on $\mathbb R^k$. Assume that $\bar Q^N_{k+1}(0)=0$ almost surely for all sufficiently large $N$, and that the diffusion-scaled initial values $(\bar Q^{d(N)}_1(0),\dots,\bar Q^{d(N)}_k(0))$ converge in distribution to $\nu$. Then:
--   1. **Uniqueness.** For every driving path and initial value, the equations (2.4) with the constraint $\bar Q_1\le0$ and a regulator $U_1$ (nonnegative, nondecreasing, càdlàg, with $\int_0^\infty\mathbb 1_{[\bar Q_1(t)<0]}dU_1(t)=0$) have at most one solution.
--   2. **Convergence.** If
--   $$\frac{d(N)}{\sqrt N\,\log N}\to\infty,$$
--   then $\{\bar Q^{d(N)}(t)\}_{t\ge0}$ converges weakly in $D_{\ell_1}[0,\infty)$ to a limit $\{\bar Q(t)\}_{t\ge0}$ with $\bar Q_i\equiv0$ for $i\ge k+1$. The first $k$ coordinates $(\bar Q_1,\dots,\bar Q_k)$, with the regulator $U_1$, solve
--   $$\begin{aligned}\bar Q_1(t)&=\bar Q_1(0)+\sqrt2\,W(t)-\beta t+\int_0^t\big(-\bar Q_1(s)+\bar Q_2(s)\big)ds-U_1(t),\\ \bar Q_2(t)&=\bar Q_2(0)+U_1(t)-\int_0^t\big(\bar Q_2(s)-\bar Q_3(s)\big)ds,\\ \bar Q_i(t)&=\bar Q_i(0)-\int_0^t\big(\bar Q_i(s)-\bar Q_{i+1}(s)\big)ds,\quad i=3,\dots,k,\end{aligned}$$
--   where $W$ is a standard Brownian motion and $\bar Q(0)$ has law $\nu$ and is independent of $W$.
--
--   The theorem says that sampling $d(N)\gg\sqrt N\log N$ servers per arrival already gives the same diffusion-level behaviour as the ordinary JSQ policy, which inspects all $N$ servers.
--
--   **Formalization Note** Several conventions are fixed in Lean.
--   - The space $D_{\mathbb S}[0,\infty)$ of the statement is read as $\ell_1$-valued càdlàg paths. Weak convergence to the continuous limit is stated in coupling form.
--   - The initial convergence is joint convergence of the $k$-vector. The page states convergence of each coordinate, which does not determine the limit.
--   - The initial value of the limit is independent of $W$.
--   - The constraint $\bar Q_1\le0$, implicit in the paper, is part of the solution concept.
--   - Uniqueness is pathwise, for every driving path.
--   - The system hypotheses are required for all large $N$. Probability spaces are taken in `Type`.
-- source:
--   Mukherjee, Borst, van Leeuwaarden & Whiting, Universality of Power-of-d Load Balancing in Many-Server Systems, arXiv:1612.00723v2, pp. 7–8, Theorem 2.4 (with the standing assumption of §2.3, p. 7)

import Mathlib
import Definitions.Def_PowerOfDUniversality_Diffusion_HalfinWhitt

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Diffusion

/-- **Theorem 2.4 (Universality of diffusion limit for JSQ(d(N)) scheme)** (Mukherjee, Borst,
van Leeuwaarden & Whiting, arXiv:1612.00723v2, pp. 7–8). Let `β > 0` (the Halfin–Whitt parameter of
§2.3), `b ≥ 2` (possibly `⊤`), `k ≥ 2`, and let `ν` be a probability measure on `ℝ^k`.
1. *Uniqueness:* for every driving path `w` and initial value `x`, any two solutions of (2.4)
   (`Solves24`) coincide at every time `t ≥ 0`.
2. *Convergence:* for every Halfin–Whitt sequence of JSQ(d(N)) systems with `N = 1, 2, …` servers
   (`IsHWSequence` with `Ns = id`: `(N − λ(N))/√N → β`, `Q̄^N_{k+1}(0) = 0` a.s. for all large `N`,
   and `(Q̄^N_1(0), …, Q̄^N_k(0))` converging jointly in law to `ν`) with
   `d(N)/(√N log N) → ∞`, the diffusion-scaled occupancy processes `Q̄^{d(N)}` converge weakly in
   `D_{ℓ¹}[0, ∞)` to a limit `Q̄` with `Q̄_i ≡ 0` for `i ≥ k + 1` whose first `k` coordinates,
   with a regulator `U₁`, solve (2.4) driven by a standard Brownian motion `W` from an initial
   value with law `ν` independent of `W` (`HasDiffusionLimit24`). -/
theorem theorem_2_4 (β : ℝ) (hβ : 0 < β) (b : ℕ∞) (hb : 2 ≤ b) (k : ℕ) (hk : 2 ≤ k)
    (ν : Measure (Fin k → ℝ)) (d : ℕ → ℕ) (lam : ℕ → ℝ) {Ω : ℕ → Type}
    [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N)) (Q₀ : ∀ N, Ω N → ℕ → ℕ)
    (E : ∀ N, Ω N → ℕ → ℝ) (M : ∀ N, Ω N → ℕ → Mark)
    (hseq : IsHWSequence β b k ν (fun N => N) d lam P Q₀ E M)
    (hd : Tendsto (fun N : ℕ => (d N : ℝ) / (Real.sqrt N * Real.log N)) atTop atTop) :
    (∀ (w : ℝ → ℝ) (x : Fin k → ℝ) (Q Q' : ℝ → ℕ → ℝ) (U U' : ℝ → ℝ),
        Solves24 β k w x Q U → Solves24 β k w x Q' U' →
        ∀ t : ℝ, 0 ≤ t → Q t = Q' t ∧ U t = U' t) ∧
    HasDiffusionLimit24 β k ν P
      (fun N ω => diffusionProcess b N (Q₀ N ω) (E N ω) (M N ω)) := by sorry

end PowerOfDUniversality.Diffusion
