-- Prove2me | Theorems.Thm_SmoothCCP_PenaltyModel_proposition_5_1
-- name    : SmoothCCP.PenaltyModel.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:37.987414+00:00
-- url     : https://prove2.me/theorems/c1d80bcd-654e-4bdc-8582-faf0ee86bbde
-- title:
--   Proposition 5.1 — a local minimum x* of (5.1) gives the local minimum (x*, C^N(x*)) of the lifted problem (5.2)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, let $g=(g_1,\dots,g_p)$ be differentiable, let $c_1,\dots,c_m$ ($m\ge1$) be constraint functions and $\xi_1,\dots,\xi_N$ a fixed sample. Let $\varepsilon>0$, $\gamma_\varepsilon$ the quartic kernel (2.6), $0<\alpha<1$, $N\ge1$, $(1-\alpha)N\notin\mathbb Z$, and $Q_\varepsilon$ the smoothed quantile of (2.3). Consider
--   $$
--   \text{(5.1)}\quad\min_{x\in\mathbb R^n} f(x)\ \text{ s.t. }\ g(x)\le0,\ Q_\varepsilon(C^N(x))\le0,
--   $$
--   $$
--   \text{(5.2)}\quad\min_{x\in\mathbb R^n,\,z\in\mathbb R^N} f(x)\ \text{ s.t. }\ g(x)\le0,\ c(x,\xi_i)\le z_i\mathbf 1_m\ (i=1,\dots,N),\ Q_\varepsilon(z)\le0 .
--   $$
--   If $x^*$ is a local minimum of (5.1), that is, $x^*$ is feasible for (5.1) and no feasible point of (5.1) near $x^*$ has a smaller objective value, then $(x^*,C^N(x^*))$ is a local minimum of (5.2): it is feasible for (5.2), and no feasible point of (5.2) near it has a smaller objective value.
--
--   The lifted problem (5.2) replaces the nonsmooth maxima $\max_j c_j(x,\xi_i)$ by auxiliary variables; the proposition says that this reformulation loses no local minimum of (5.1).
--
--   **Formalization Note** Local minima are `IsLocalMinOn` on the feasible sets, with feasibility of $x^*$ a hypothesis and feasibility of $(x^*,C^N(x^*))$ part of the conclusion. The product $\mathbb R^n\times\mathbb R^N$ carries the product topology. The quartic kernel and $(1-\alpha)N\notin\mathbb Z$ are the hypotheses of Proposition 4.1, through which the paper's proof gets monotonicity of $Q_\varepsilon$.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, Proposition 5.1, p. 16

import Mathlib
import Definitions.Def_SmoothCCP_PenaltyModel_Setting

namespace SmoothCCP.PenaltyModel

/-- Proposition 5.1, arXiv:1905.07377v2, p. 16: if x* is a local minimum of (5.1)
(min f s.t. g(x) ≤ 0, Q_ε(C^N(x)) ≤ 0), then (x*, C^N(x*)) is a local minimum of (5.2)
(min f s.t. g(x) ≤ 0, c(x, ξᵢ) ≤ zᵢ 1_m for all i, Q_ε(z) ≤ 0), with γ_ε the quartic kernel (2.6). -/
theorem proposition_5_1 {n m p N : ℕ} {Ξ : Type} (hm : 1 ≤ m) (hN : 1 ≤ N) (ξs : Fin N → Ξ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → Ξ → ℝ)
    (ε α : ℝ) (hε : 0 < ε) (hα0 : 0 < α) (hα1 : α < 1) (hαN : ∀ k : ℤ, (1 - α) * N ≠ k)
    (hg : ∀ k, Differentiable ℝ (g k))
    (xstar : EuclideanSpace ℝ (Fin n))
    (hfeas : (∀ k, g k xstar ≤ 0) ∧ smoothQuantile ε (quarticGamma ε) α (CN hm c ξs xstar) ≤ 0)
    (hmin : IsLocalMinOn f
      {x | (∀ k, g k x ≤ 0) ∧ smoothQuantile ε (quarticGamma ε) α (CN hm c ξs x) ≤ 0} xstar) :
    (xstar, CN hm c ξs xstar) ∈
        {q : EuclideanSpace ℝ (Fin n) × (Fin N → ℝ) | (∀ k, g k q.1 ≤ 0) ∧
          (∀ i j, c j q.1 (ξs i) ≤ q.2 i) ∧ smoothQuantile ε (quarticGamma ε) α q.2 ≤ 0} ∧
    IsLocalMinOn (fun q : EuclideanSpace ℝ (Fin n) × (Fin N → ℝ) => f q.1)
      {q | (∀ k, g k q.1 ≤ 0) ∧ (∀ i j, c j q.1 (ξs i) ≤ q.2 i) ∧
        smoothQuantile ε (quarticGamma ε) α q.2 ≤ 0}
      (xstar, CN hm c ξs xstar) := by sorry

end SmoothCCP.PenaltyModel
