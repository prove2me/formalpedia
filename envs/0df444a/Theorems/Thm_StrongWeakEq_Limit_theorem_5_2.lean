-- Prove2me | Theorems.Thm_StrongWeakEq_Limit_theorem_5_2
-- name    : StrongWeakEq.Limit.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:28.832264+00:00
-- url     : https://prove2.me/theorems/9cba508d-0117-4ec7-a293-e72d43cd2521
-- title:
--   Theorem 5.2, p. 17 — a limit Q* ∈ 𝒬 of generators of discretized equilibria satisfies (3.10) for all (i, Q) and is a weak equilibrium
-- statement:
--   Consider the continuous-time model of §2 under its standing assumptions (2.1)–(2.3). Assume (5.8) and that $f(\cdot,i,\cdot)$ is continuous on $[0,\infty)\times D_i$ for every $i\in S$. Let $(\delta_n)_{n\in\mathbb N}$ be positive reals with $\delta_n\downarrow0$, and for each $n$ let $u^n\in\mathcal A^n$ be an equilibrium of the discretized problem $V^n$ (payoff $\kappa^n$ of (5.9), admissible transition matrices $\mathcal A^n$ of (5.11), Definition 5.1), with generator $Q^n=Q^{u^n,n}=\frac1{\delta_n}(u^n-I)\in\mathcal Q$. If there exists $Q^*\in\mathcal Q$ such that, along a subsequence, $Q^n\to Q^*$, then
--
--   1. $Q^*$ satisfies (3.10) for all $(i,Q)\in S\times\mathcal Q$:
--   $$
--   \Gamma^{Q^*}(Q^*_i)\ \ge\ \Gamma^{Q^*}(Q_i),\qquad \Gamma^{Q^*}(q)=f(0,i,q)+q\cdot F(Q^*);
--   $$
--   2. $Q^*$ is a weak equilibrium in the sense of Definition 2.1: for all $Q\in\mathcal Q$ and $i\in S$,
--   $$
--   \liminf_{\varepsilon\downarrow0}\frac{F(i,Q^*)-F(i,Q\otimes_\varepsilon Q^*)}{\varepsilon}\ge0 .
--   $$
--
--   Thus every limit point of equilibria of the time-discretized problems is an equilibrium of the continuous-time problem in the weak sense; the paper's Example 5.1 shows it need not be a strong equilibrium.
--
--   **Formalization Note** The subsequence is a strictly increasing map $\varphi:\mathbb N\to\mathbb N$ with $Q^{\varphi(k)}\to Q^*$. "$f(\cdot,i,\cdot)$ is continuous" is read as joint continuity on $[0,\infty)\times D_i$. Condition (3.3) of Theorem 3.1, through which the page passes from (3.10) to the weak-equilibrium property, is **not** assumed, as on the page; the second conclusion is nevertheless true under (2.1)–(2.3), because for a time-homogeneous chain the shifted payoff $F_\varepsilon(i,Q^*)$ tends to $F(i,Q^*)$ as $\varepsilon\downarrow0$ without (3.3). The weak-equilibrium property is encoded as: for every $\eta>0$, eventually as $\varepsilon\downarrow0$ the difference quotient is $\ge-\eta$. Summability of $H^n$ and integrability of $F$ follow from (2.3) and (5.8) and are not assumed. States are `Fin N`.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 17, Theorem 5.2 (proof p. 18 and Appendix B.2, pp. 28–29)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel
import Definitions.Def_StrongWeakEq_Limit_Discretization

namespace StrongWeakEq.Limit

open Filter Topology

/-- Theorem 5.2, p. 17: assume (2.1)–(2.3), (5.8) and that `f(·,i,·)` is continuous on
`[0,∞) × Dᵢ`. Let `δₙ ↓ 0`, let `uⁿ` be an equilibrium of the problem discretized with mesh
`δₙ`, and suppose `Qⁿ = (uⁿ − I)/δₙ → Q* ∈ 𝒬` along the subsequence `φ`. Then `Q*` satisfies
(3.10), `Γ^{Q*}(Q*ᵢ) ≥ Γ^{Q*}(Qᵢ)` for all `(i, Q) ∈ S × 𝒬`, and `Q*` is a weak equilibrium. -/
theorem theorem_5_2 {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : StrongWeakEq.Existence.Standing D f)
    (h58 : EventuallyNonincreasing D f)
    (hcont : ∀ i, ContinuousOn (fun p : ℝ × (Fin N → ℝ) => f p.1 i p.2) (Set.Ici 0 ×ˢ D i))
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n) (hδanti : Antitone δ) (hδlim : Tendsto δ atTop (𝓝 0))
    (u : ℕ → Matrix (Fin N) (Fin N) ℝ)
    (hu : ∀ n, StrongWeakEq.Discrete.IsDEquilibrium (admRows D (δ n)) (kappaN f (δ n)) (u n))
    (Qs : Matrix (Fin N) (Fin N) ℝ) (hQs : Qs ∈ StrongWeakEq.Existence.Controls D) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : Tendsto (fun k => genOf (δ (φ k)) (u (φ k))) atTop (𝓝 Qs)) :
    (∀ i, ∀ Q ∈ StrongWeakEq.Existence.Controls D, StrongWeakEq.Existence.Gamma f Qs i (Q i) ≤ StrongWeakEq.Existence.Gamma f Qs i (Qs i)) ∧
      StrongWeakEq.Existence.IsWeakEquilibrium D f Qs := by sorry

end StrongWeakEq.Limit
