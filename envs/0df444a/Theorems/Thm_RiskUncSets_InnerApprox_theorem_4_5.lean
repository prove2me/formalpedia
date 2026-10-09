-- Prove2me | Theorems.Thm_RiskUncSets_InnerApprox_theorem_4_5
-- name    : RiskUncSets.InnerApprox.theorem_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:07:13.424504+00:00
-- url     : https://prove2.me/theorems/b72f4dae-9ddb-4602-868f-dbce24712280
-- title:
--   Theorem 4.5, p. 1493 — the largest centrally symmetric distortion permutohull inside a polytope 𝒰 is given by the LP (15), and it is a distortion set iff λ* ≤ 1/(1 − N q_min)
-- statement:
--   Let $N \ge 1$, let $\hat q \in \hat\Delta^N_{\mathrm{sym}}$ be a centrally symmetric generator, let $\mathcal A = \{a_1,\dots,a_N\} \subset \mathbb R^n$ have sample mean $\hat a = Ae_N$, and let
--   $$\mathcal U = \{a \in \mathbb R^n : u_k' a \ge v_k,\ k = 1,\dots,m\}$$
--   be the polyhedron (14), with $\hat a \in \mathcal U$. Consider the linear program
--   $$\begin{aligned}\text{maximize}\quad & \lambda\\ \text{subject to}\quad & q = \lambda\hat q + (1-\lambda)e/N,\\ & e'(s_k + t_k) \ge v_k \quad \forall k \in \{1,\dots,m\},\\ & s_{k,i} + t_{k,j} \le (u_k' a_j)\, q_i \quad \forall (i,j) \in \{1,\dots,N\}^2,\ \forall k \in \{1,\dots,m\},\end{aligned}\tag{15}$$
--   in the variables $s_k, t_k, q \in \mathbb R^N$ and $\lambda \in \mathbb R$, and suppose its optimal value $\lambda^*$ is attained. Put $q^* = \lambda^*\hat q + (1-\lambda^*)e_N$. Then:
--
--   1. $\Pi_{q^*}(\mathcal A) \subseteq \mathcal U$;
--   2. for every $\lambda \in \mathbb R$ with $\Pi_{\lambda\hat q + (1-\lambda)e_N}(\mathcal A) \subseteq \mathcal U$, one has $\Pi_{\lambda\hat q + (1-\lambda)e_N}(\mathcal A) \subseteq \Pi_{q^*}(\mathcal A)$;
--   3. if $N\hat q_{\min} < 1$, where $\hat q_{\min} = \min_i \hat q_i$, then $q^* \in \hat\Delta^N$ (the approximating set corresponds to a distortion risk measure) if and only if
--   $$\lambda^* \le \frac{1}{1 - N\hat q_{\min}}.\tag{16}$$
--
--   Parts 1 and 2 say that among the centrally symmetric permutohulls $\Pi_q(\mathcal A)$ obtained by mixing $\hat q$ with $e_N$ and contained in $\mathcal U$, the one given by the solution of (15) is the largest; by Lemma 4.2 this is largest in the $\|\cdot\|_{\hat q,\mathcal A}$ sense, since these sets are the balls $\hat a + |\lambda|\,\tilde\pi_{\hat q}(\mathcal A)$. The result turns the search for the best distortion-risk inner approximation of an arbitrary polyhedral uncertainty set into a linear program.
--
--   **Formalization Note** "Largest in the $\|\cdot\|_{\hat q,\mathcal A}$ sense" is stated as set containment rather than through the gauge, because Mathlib's `gauge` takes the junk value $0$ on the degenerate set $\{0\}$ (at $\lambda = 0$). The optimal value is a hypothesis (`IsGreatest` over the feasible set of (15)), as the page presupposes "the optimal value $\lambda^*$ of (15)"; when (15) is unbounded (for instance $m = 0$, or $\Pi_{\hat q}(\mathcal A) = \{\hat a\}$) no such $\lambda^*$ exists and the theorem says nothing, as on the page. "Corresponds to a distortion risk measure" is read, as the proof reads it, as $q^* \in \hat\Delta^N$, the parameter set of the distortion risk measures by Theorem 4.2 of the paper (mission 1 of this series). $q_{\min}$ is not defined on the page and is read as $\min_i \hat q_i$; the hypothesis $N\hat q_{\min} < 1$ ($\hat q \ne e_N$) is added to part 3 because (16) divides by $1 - N\hat q_{\min}$. The set $\mathcal U$ is not assumed bounded (the page says "polytope"; no part needs boundedness, so this is a generalization). Indices are $0$-based in Lean.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), p. 1493, Theorem 4.5, (14)–(16)

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
noncomputable section

namespace RiskUncSets.InnerApprox

/-- Theorem 4.5: with `λ*` the optimal value of (15), the mixture
`q* = λ*q̂ + (1−λ*)e_N` has `Π_{q*}(𝒜) ⊆ 𝒰`, its permutohull contains that of every
mixture contained in `𝒰`, and (16): `q* ∈ Δ̂ᴺ` iff `λ* ≤ 1/(1 − N q̂_min)`. -/
theorem theorem_4_5 {N n m : ℕ} (hN : 0 < N) (qh : Fin N → ℝ)
    (hqh : qh ∈ symRestrictedSimplex N) (a : Fin N → Fin n → ℝ)
    (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) (hmean : sampleMean a ∈ polytope u v)
    (lamStar : ℝ) (hopt : IsGreatest {lam | LP15Feasible qh a u v lam} lamStar) :
    permutohull (mix qh lamStar) a ⊆ polytope u v ∧
    (∀ lam : ℝ, permutohull (mix qh lam) a ⊆ polytope u v →
      permutohull (mix qh lam) a ⊆ permutohull (mix qh lamStar) a) ∧
    ((N : ℝ) * (⨅ i, qh i) < 1 →
      (mix qh lamStar ∈ restrictedSimplex N ↔
        lamStar ≤ 1 / (1 - (N : ℝ) * ⨅ i, qh i))) := by sorry

end RiskUncSets.InnerApprox
