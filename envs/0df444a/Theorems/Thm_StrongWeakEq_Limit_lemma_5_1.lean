-- Prove2me | Theorems.Thm_StrongWeakEq_Limit_lemma_5_1
-- name    : StrongWeakEq.Limit.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:21.843112+00:00
-- url     : https://prove2.me/theorems/5902afd1-c22d-4525-bb0a-537f489c62e4
-- title:
--   Lemma 5.1, p. 17 — along the subsequence with Qⁿ → Q*, the discrete continuation values Hⁿᵢ(uⁿ) converge to Fᵢ(Q*)
-- statement:
--   Consider the continuous-time model of §2 under its standing assumptions (2.1)–(2.3). Assume (5.8) and that $f(\cdot,i,\cdot)$ is continuous on $[0,\infty)\times D_i$ for every $i\in S$. Let $(\delta_n)_{n\in\mathbb N}$ be positive reals with $\delta_n\downarrow0$, and for each $n$ let $u^n\in\mathcal A^n$ be an equilibrium of the discretized problem $V^n$ (payoff $\kappa^n$ of (5.9), admissible matrices $\mathcal A^n$ of (5.11)), with generator $Q^n=Q^{u^n,n}=\frac1{\delta_n}(u^n-I)\in\mathcal Q$. Suppose there is $Q^*\in\mathcal Q$ such that, along a subsequence $(n_k)$, $Q^{n_k}\to Q^*$. Then for every $i\in S$,
--
--   $$
--   H^{n_k}_i(u^{n_k})\ \longrightarrow\ F_i(Q^*)=\mathbb E_{i,Q^*}\Big[\int_0^\infty f(t,X_t,Q^*_{X_t})\,dt\Big]\qquad(k\to\infty),
--   $$
--
--   where $H^n_i(u^n)=\mathbb E_{i,u^n}\big[\sum_{k\ge0}\kappa^n(k+1,X_k,u^n_{X_k})\big]$ is the continuation value (5.13).
--
--   This is the convergence of the discrete continuation values to the continuous-time payoff vector that drives the passage to the limit in Theorem 5.2.
--
--   **Formalization Note** The subsequence is a strictly increasing map $\varphi:\mathbb N\to\mathbb N$, and both the convergence hypothesis and the conclusion are along $\varphi$. "$f(\cdot,i,\cdot)$ is continuous" is read as joint continuity on $[0,\infty)\times D_i$ with the product topology, which is how the proof uses it (uniform continuity on $[0,T]\times\{q\in D_i:\|q\|\le a\}$, p. 29). $\delta_n\downarrow0$ is: $\delta_n>0$, $(\delta_n)$ nonincreasing, $\delta_n\to0$. $H^n$ is a `tsum` and $F$ a Bochner integral; their summability and integrability follow from (2.3) and (5.8) and are not assumed. Only $u^n\in\mathcal A^n$ is used by the argument, but the hypothesis is stated as on the page, for the equilibria $u^n$ of p. 17. States are `Fin N`.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 17, Lemma 5.1 (proof Appendix B.2, pp. 28–29)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel
import Definitions.Def_StrongWeakEq_Limit_Discretization

namespace StrongWeakEq.Limit

open Filter Topology

/-- Lemma 5.1, p. 17: assume (2.1)–(2.3), (5.8) and that `f(·,i,·)` is continuous on
`[0,∞) × Dᵢ`. Let `δₙ ↓ 0`, let `uⁿ` be an equilibrium of the problem discretized with mesh
`δₙ`, and suppose `Qⁿ = (uⁿ − I)/δₙ → Q* ∈ 𝒬` along the subsequence `φ`. Then
`Hⁿᵢ(uⁿ) → Fᵢ(Q*)` along `φ`, for every `i`. -/
theorem lemma_5_1 {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : StrongWeakEq.Existence.Standing D f)
    (h58 : EventuallyNonincreasing D f)
    (hcont : ∀ i, ContinuousOn (fun p : ℝ × (Fin N → ℝ) => f p.1 i p.2) (Set.Ici 0 ×ˢ D i))
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n) (hδanti : Antitone δ) (hδlim : Tendsto δ atTop (𝓝 0))
    (u : ℕ → Matrix (Fin N) (Fin N) ℝ)
    (hu : ∀ n, StrongWeakEq.Discrete.IsDEquilibrium (admRows D (δ n)) (kappaN f (δ n)) (u n))
    (Qs : Matrix (Fin N) (Fin N) ℝ) (hQs : Qs ∈ StrongWeakEq.Existence.Controls D) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : Tendsto (fun k => genOf (δ (φ k)) (u (φ k))) atTop (𝓝 Qs)) :
    ∀ i, Tendsto (fun k => StrongWeakEq.Discrete.dH (kappaN f (δ (φ k))) (u (φ k)) i) atTop (𝓝 (StrongWeakEq.Existence.payoff f Qs i)) := by sorry

end StrongWeakEq.Limit
