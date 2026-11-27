-- Prove2me | Theorems.Thm_RelaxedEqMDP_Discrete_Supplement_theorem_5_1
-- name    : RelaxedEqMDP.Discrete.Supplement.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T19:11:53.397708+00:00
-- url     : https://prove2.me/theorems/2bbe12dc-8728-49ea-a6ab-159ff519063d
-- title:
--   Theorem 5.1 (corrected: δ(kh) in (5.4), uniform Riemann tails) — equilibria of the step-hn discretizations converge to continuous-time (regular) relaxed equilibria
-- statement:
--   Let $d,\ell>0$ and $\mathcal S=\{1,\dots,d\}$, let $U\subset\mathbb R^\ell$ be compact with $\mathrm{Leb}(U)>0$, and let each $u\in U$ carry a rate matrix $q^u$ ($q^u_{ij}\ge0$ for $j\ne i$, rows summing to $0$). Let $f(t,i,u)$ be the reward and $\delta$ the discount ($\delta:[0,\infty)\to[0,1]$ nonincreasing, $\delta(0)=1$), and assume **Assumption 3.1**: $\int_0^\infty\big(\sup_{i\in\mathcal S,u\in U}|f(s,i,u)|+\delta(s)\big)\,ds<\infty$. Assume **Assumption 2.2** with $q$ in place of $p$ and **Assumption 2.3**, and suppose that $f(\cdot,i,u)$ and $\delta$ are continuous on $[0,\infty)$. Take $h_n\in(0,1]$ with $h_n\downarrow0$ such that every $p_{h_n}^u=h_nq^u+I$ ($u\in U$) is a transition matrix, and assume that $f$ has **uniform Riemann tails** along $(h_n)$: for a majorant $b(s)\ge\sup_{i,u\in U}|f(s,i,u)|$ the series $\sum_kb(kh_n)$ converge and $\lim_{T\to\infty}\sup_nh_n\sum_{kh_n\ge T}b(kh_n)=0$. The step-$h$ problem has transition matrices $p_h^u$ and rewards $f_h(k,i,u)=f(kh,i,u)h$ ((5.1)–(5.3)); its regularized version (5.4) is $J^\pi_{h\lambda}$ with the discount $\delta(kh)$.
--
--   1. **(a)** Fix $\lambda>0$ and let each $\pi^n\in\Pi_r$ be a regular relaxed equilibrium for the step-$h_n$ regularized problem. Then along a subsequence the density of $\pi^n(i)$ converges almost everywhere on $U$ to the density of some $\pi^\infty(i)$, for every $i$, and $\pi^\infty\in\Pi_r$ is a regular relaxed equilibrium for (3.2).
--   2. **(b)** Let each $\pi^n\in\Pi$ be a relaxed equilibrium for the step-$h_n$ problem (5.3). Then along a subsequence $\pi^n(i)\to\pi^\infty(i)$ weakly for every $i$, and $\pi^\infty\in\Pi$ is a relaxed equilibrium for (3.1).
--
--   The theorem justifies computing continuous-time relaxed equilibria through discrete-time ones as the time step goes to zero.
--
--   **Formalization Note** The discretized problems and their equilibria are the base mission's objects applied to $(p_{h_n},f_{h_n},\delta_{h_n},h_n\lambda)$. One subsequence serves all states. Densities are taken with respect to Lebesgue measure on $U$.
--
--   Differences from the source:
--   - correction: (5.4): J^{h,π}_λ = J^π_{hλ} = E_i[Σ_k (f_h^{π(X^h_k)}(k, X^h_k) + hλδ(k)ℋ(π(X^h_k)))], discount evaluated at the step index k → the discount is sampled on the grid, δ_h(k) = δ(k h_n): the base IsRegularRelaxedEq with (p_{h_n}, f_{h_n}, δ_{h_n}, h_n λ); reason: Printed δ(k) fails even for smooth exponential rewards and uniformly controlled Riemann tails: DISPROOF.md §3 gives an explicit three-state family of discrete equilibria converging to a non-equilibrium of (3.2). Sampling δ(kh) restores the Riemann sum of the entropy term in (3.2), exactly as the final identity of the proof on p. 26 requires.
--   - correction: no condition on the Riemann tails of f; the proof of Lemma 5.1 (A.21), p. 25, bounds h_n Σ_{k>T/h_n} sup|f(kh_n)| by ∫_T^∞ sup|f| → added UniformRiemannTail: a majorant b ≥ sup_{i,u∈U}|f(s,i,u)| with Σ_k b(kh_n) < ∞ for each n and lim_{T→∞} sup_n h_n Σ_{kh_n ≥ T} b(kh_n) = 0; reason: the step (A.21) needs it, and without it part (b) fails: S = {1,2,3}, U = [0,1], q^u_1 = (−1, u, 1 − u), states 2 and 3 absorbing, f(t,1,·) = f(t,3,·) = 0, f(t,2,·) = e^{−2t} − Σ_m 2^m τ_m(t) with tents τ_m of height 1 and half-width 8^{−m} at T_m = m + 2^{−m}, h_n = 2^{−n}; every hypothesis holds (Assumptions 3.1, 2.2, 2.3, continuity, p_{h_n} stochastic, each discretized problem summable); the spike at T_n alone contributes −1 to the grid sum, so V^{h_n}(2) ≤ 1/2 − 1 + o(1) < 0 = V^{h_n}(3) and every discretized relaxed equilibrium uses u = 0 at state 1, while in continuous time J̃(2) = 1/2 − Σ_m 4^{−m} = 1/6 > 0 = J̃(3) forces u = 1, so the limit is not a relaxed equilibrium (DISPROOF.md). The condition holds whenever sup_{i,u}|f(s,i,u)| has a nonincreasing integrable majorant (Huang–Zhou's eventual monotonicity, their (5.8)). It excludes rewards whose grid sums carry mass that the time integral does not see; it also makes each discretized problem satisfy Assumption 2.1
--   - reading: 'for a step size h > 0 small enough' (p. 17), the discretized chain having transition matrix p_h (5.1) → every p_{h_n} = h_n q + 1 is a transition matrix on U (base Standing U (p_{h_n}) for all n); reason: equivalent to h_n max_{i,u∈U}|q^u_ii| ≤ 1; since h_n ↓ 0 and the conclusions hold along a subsequence, this excludes only finitely many initial steps
--   - reading: (a) 'π^n(i) ∈ D(U) converges pointwise to some π^∞(i) ∈ D(U), up to a subsequence' → one strictly increasing φ for all i; the densities dπ^{φ(k)}(i)/du converge to dπ^∞(i)/du Lebesgue-a.e. on U, and π^∞ ∈ Π_r; reason: densities in D(U) are determined only up to null sets, so pointwise convergence is read almost everywhere; the subsequence is common to the finitely many states, as in the proof (p. 26)
--   - reading: (b) 'π^n(i) ∈ P(U) converges weakly to some π^∞(i) ∈ P(U), up to a subsequence' → one strictly increasing φ for all i with π^{φ(k)}(i) → π^∞(i) weakly (tested against bounded continuous functions on ℝ^ℓ), and π^∞ ∈ Π; reason: weak convergence of measures carried by U, as in the base mission's WeakTendsto; the subsequence is common to all states, as in the proof (p. 27)
--   - encoding: {h_n} in (0, 1] with h_n ↓ 0 → IsLamSeq h: 0 < h_n ≤ 1, h antitone, h_n → 0; reason: the base mission's encoding of a sequence decreasing to 0
--   - reading: Assumption 2.2 'with p^u_i therein replaced by q^u_i': sup of |f(t,i,u₁) − f(t,i,u₂)| + |q^{u₁}_i − q^{u₂}_i| over |u₁ − u₂| finite, uniformly in t → Assumption22CT: Θ > 0 with |f(t,i,u₁) − f(t,i,u₂)| + |q^{u₁}_i − q^{u₂}_i| ≤ Θ|u₁ − u₂| for all t ≥ 0, i and u₁, u₂ ∈ U (Euclidean norms); reason: (2.16) with q for p, over the continuous time set [0,∞); a positive bound exists whenever the supremum is finite
--   - reading: Assumption 2.3: a cone with vertex u, half-angle ι and height ϑ inside U (Δ_ι printed as a double cone) → the published base Assumption23: a one-nappe cone {v : ⟨v − u, a⟩ ≥ |v − u| cos ι} cut by the open ball B_ϑ(u); reason: the base mission's disclosed reading of Assumption 2.3, reused unchanged
--   - reading: the integrals f^µ(t,i) = ∫_U f(t,i,u)µ(du), Q^µ_ij = ∫_U q^u_ij µ(du) and the time integrals (3.1)–(3.5), with no measurability stated → (s,u) ↦ f(s,i,u) measurable on [0,∞) × U and u ↦ q^u_ij measurable on U (MeasMapsCT U f q); reason: the integrals presuppose it; it is the standing measurability convention, as in the base mission's MeasMaps
--   - reading: ℓ ∈ ℕ and S = {1, …, d} with d ∈ ℕ (p. 4, reused in §3) → 0 < ℓ and 0 < d; reason: The source uses positive natural dimensions; Fin d indexes the d states from zero instead of one.
--   - encoding: f : [0,∞) × S × U → ℝ, δ : [0,∞) → [0,1] → f : ℝ → Fin d → A ℓ → ℝ and δ : ℝ → ℝ, with every hypothesis and integral restricted to times s ≥ 0 and actions u ∈ U; reason: The values outside the source domain do not enter the hypotheses or the values of admissible controls; measurability is stated on the source-domain subtypes.
--   - encoding: values (3.1), (3.2), (3.4), (3.5) as expectations E_i[∫_0^∞ … ds] over the controlled chain X^π → ∫_0^∞ (exp(sQ^π) r(s))_i ds with Q^π the relaxed generator (rows Q^{π(i)}_i) and r(s) the vector of averaged rewards; reason: the law of X^π_s started at i is row i of exp(sQ^π), the continuous-time analogue of Remark 2.1; the values are the same
--   - encoding: J̃^{π′⊗_επ} for the control that uses π′ on [0, ε) and π on [ε, ∞) → ∫_0^ε (exp(sQ^{π′}) r^{π′}(s))_i ds + (exp(εQ^{π′}) Ṽ^π(ε))_i (and the same with r_λ and Ṽ_λ); reason: this is the value of the concatenation by the Markov property at time ε; no process is constructed
--   - encoding: lim sup_{ε↓0} (J̃^{π′⊗_επ}(i) − J̃^π(i))/ε ≤ 0 in Definition 3.1 → for every η > 0 the quotient is ≤ η for all sufficiently small ε > 0; reason: equivalent to lim sup ≤ 0, and avoids Filter.limsup on ℝ, which returns a junk value for unbounded functions
-- source:
--   Bayraktar, Huang, Wang, Zhou, Relaxed Equilibria for Time-Inconsistent Markov Decision Processes, arXiv:2307.04227v2, p. 18, Theorem 5.1 and (5.4); p. 17, (5.1)–(5.3); proof: pp. 24–27, Appendix A.6–A.7

import Mathlib
import Definitions.Def_RelaxedEqMDP_Discrete_Setting
import Definitions.Def_RelaxedEqMDP_Discrete_Supplement_ContinuousTime
import Definitions.Def_RelaxedEqMDP_Discrete_Supplement_Discretization

open MeasureTheory Filter Topology Matrix

namespace RelaxedEqMDP.Discrete.Supplement

/-- Theorem 5.1, p. 18 (corrected): under Assumptions 3.1, 2.2 (with `q^u_i` for `p^u_i`) and 2.3,
with `f(·,i,u)` and `δ(·)` continuous on `[0,∞)`, take `h_n ∈ (0,1]` with `h_n ↓ 0` such that every
`p_{h_n} = h_n q + 1` is a transition matrix, and (added) the rewards have uniform Riemann tails along
`h_n`.
(a) Given `λ > 0`, if each `π^n ∈ Π_r` is a regular relaxed equilibrium for `J^{h_n,π}_λ` (5.4), with
the discount sampled as `δ(k h_n)`, then along a subsequence the densities of `π^n(i)` converge a.e.
on `U` to the density of some `π^∞(i)`, and `π^∞ ∈ Π_r` is a regular relaxed equilibrium for (3.2).
(b) If each `π^n ∈ Π` is a relaxed equilibrium for `J^{h_n,π}` (5.3), then along a subsequence
`π^n(i) → π^∞(i)` weakly for every `i`, and `π^∞ ∈ Π` is a relaxed equilibrium for (3.1). -/
theorem theorem_5_1 {d ℓ : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (U : Set (A ℓ))
    (q : A ℓ → Matrix (Fin d) (Fin d) ℝ) (f : ℝ → Fin d → A ℓ → ℝ) (δ : ℝ → ℝ)
    (Theta iota vartheta : ℝ) (hS : StandingCT U q) (hM : MeasMapsCT U f q)
    (h31 : Assumption31 U f δ) (h22 : Assumption22CT U f q Theta)
    (h23 : Assumption23 U iota vartheta)
    (hfc : ∀ i, ∀ u ∈ U, ContinuousOn (fun s => f s i u) (Set.Ici 0))
    (hδc : ContinuousOn δ (Set.Ici 0))
    (h : ℕ → ℝ) (hh : IsLamSeq h) (hph : ∀ n, Standing U (ph q (h n)))
    (htail : UniformRiemannTail U f h) :
    (∀ lam : ℝ, 0 < lam → ∀ pol : ℕ → Control d ℓ,
        (∀ n, IsRegularRelaxedEq U (ph q (h n)) (fh f (h n)) (deltah δ (h n)) (h n * lam)
          (pol n)) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ polInf : Control d ℓ, IsRegular U polInf ∧
          (∀ i, ∀ᵐ u ∂(volume.restrict U),
            Tendsto (fun k => density U (pol (φ k) i) u) atTop (𝓝 (density U (polInf i) u))) ∧
          IsRegularRelaxedEqCT U q f δ lam polInf) ∧
      ∀ pol : ℕ → Control d ℓ,
        (∀ n, IsRelaxedEq U (ph q (h n)) (fh f (h n)) (pol n)) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ polInf : Control d ℓ, IsRelaxed U polInf ∧
          (∀ i, WeakTendsto (fun k => pol (φ k) i) (polInf i)) ∧
          IsRelaxedEqCT U q f polInf := by sorry
end RelaxedEqMDP.Discrete.Supplement
