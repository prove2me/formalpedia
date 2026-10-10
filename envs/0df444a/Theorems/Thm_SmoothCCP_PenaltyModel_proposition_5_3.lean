-- Prove2me | Theorems.Thm_SmoothCCP_PenaltyModel_proposition_5_3
-- name    : SmoothCCP.PenaltyModel.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:44.839222+00:00
-- url     : https://prove2.me/theorems/fccd3f39-2afb-423a-b76a-5388484929bb
-- title:
--   Proposition 5.3 — the Sℓ1QP model m(x,H;d) of (5.6) satisfies |φ_π(x+d) − m(x,H;d)| = O(‖d‖²) uniformly in x, d and ‖H‖ ≤ L_H
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ and $g=(g_1,\dots,g_p):\mathbb R^n\to\mathbb R^p$ be differentiable with Lipschitz continuous gradients. Fix a sample $\xi_1,\dots,\xi_N$ ($N\ge1$) and constraint functions $c_1,\dots,c_m$ ($m\ge1$) such that each $c_j(\cdot,\xi_i)$ is differentiable, and suppose there are $L>0$ and $L'>0$ with
--   $$
--   |c_j(x,\xi_i)-c_j(y,\xi_i)|\le L\|x-y\|,\qquad \|\nabla c_j(x,\xi_i)-\nabla c_j(y,\xi_i)\|\le L'\|x-y\| \tag{5.4–5.5}
--   $$
--   for all $x,y\in\mathbb R^n$ and all $i,j$. Let $\varepsilon>0$, let $\gamma_\varepsilon$ be the quartic kernel (2.6), let $0<\alpha<1$ with $(1-\alpha)N\notin\mathbb Z$, let $Q_\varepsilon$ be the smoothed $(1-\alpha)$-quantile of (2.3), and let $\pi>0$ and $L_H$ be fixed.
--
--   Let $\varphi_\pi$ be the exact penalty function (5.3) and $m(x,H;d)$ the piecewise quadratic model (5.6). Then $m$ is a first-order model of $\varphi_\pi$: there is a constant $K$ such that
--   $$
--   \big|\varphi_\pi(x+d)-m(x,H;d)\big|\le K\|d\|^2
--   $$
--   for all $x,d\in\mathbb R^n$ and every symmetric $H$ with $\|H\|\le L_H$.
--
--   This is the property required by the convergence theory of trust-region methods for nonsmooth composite functions: minimizing $m$ over a trust region yields steps along which $\varphi_\pi$ decreases, and limit points of the method are stationary for $\varphi_\pi$.
--
--   **Formalization Note** The constant $K$ is quantified after all data (including $L_H$) and before $x$, $d$, $H$, so it may depend on the problem but not on the point; this is the paper's $O(\|d\|^2)$ "for all $d,x\in\mathbb R^n$ and all $H$ with $\|H\|\le L_H$, for fixed $L_H$". A symmetric matrix is a self-adjoint operator on Euclidean $\mathbb R^n$, and $\|H\|$ is its operator norm. Three readings differ from the printed page: (5.4)–(5.5) are assumed for all $x,y\in\mathbb R^n$ rather than $x,y\in X$, since the conclusion ranges over all of $\mathbb R^n$ and $X=\{g\le0\}$ plays no role in $\varphi_\pi$ or $m$; they are read per component $c_j$, as the proof applies them; and the quartic kernel with $(1-\alpha)N\notin\mathbb Z$ is assumed because the proof invokes Proposition 4.1, without which $\nabla Q_\varepsilon$ need not exist. The Lipschitz constants of $\nabla f$ and $\nabla g$ are existential.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, Proposition 5.3, p. 17 (proof p. 18)

import Mathlib
import Definitions.Def_SmoothCCP_PenaltyModel_Setting

namespace SmoothCCP.PenaltyModel

/-- Proposition 5.3, arXiv:1905.07377v2, p. 17: with γ_ε the quartic kernel (2.6), (1 − α)N ∉ ℤ,
f and g differentiable with Lipschitz gradients, and each cⱼ(·, ξᵢ) differentiable and satisfying
(5.4)–(5.5) on ℝⁿ, the model m(x, H; d) of (5.6) satisfies |φ_π(x + d) − m(x, H; d)| = O(‖d‖²)
for all x, d ∈ ℝⁿ and all symmetric H with ‖H‖ ≤ L_H, the constant depending on the data and L_H
only. -/
theorem proposition_5_3 {n m p N : ℕ} {Ξ : Type} (hm : 1 ≤ m) (hN : 1 ≤ N) (ξs : Fin N → Ξ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin n) → Ξ → ℝ)
    (ε α π LH L L' : ℝ) (hε : 0 < ε) (hα0 : 0 < α) (hα1 : α < 1)
    (hαN : ∀ k : ℤ, (1 - α) * N ≠ k) (hπ : 0 < π) (hL : 0 < L) (hL' : 0 < L')
    (hf : Differentiable ℝ f)
    (hfL : ∃ Lf : ℝ, ∀ x y, ‖gradient f x - gradient f y‖ ≤ Lf * ‖x - y‖)
    (hg : ∀ k, Differentiable ℝ (g k))
    (hgL : ∃ Lg : ℝ, ∀ k x y, ‖gradient (g k) x - gradient (g k) y‖ ≤ Lg * ‖x - y‖)
    (hc : ∀ i j, Differentiable ℝ (fun x => c j x (ξs i)))
    (h54 : ∀ (x y : EuclideanSpace ℝ (Fin n)) (i : Fin N) (j : Fin m),
      |c j x (ξs i) - c j y (ξs i)| ≤ L * ‖x - y‖)
    (h55 : ∀ (x y : EuclideanSpace ℝ (Fin n)) (i : Fin N) (j : Fin m),
      ‖gradient (fun z => c j z (ξs i)) x - gradient (fun z => c j z (ξs i)) y‖ ≤ L' * ‖x - y‖) :
    ∃ K : ℝ, ∀ (x d : EuclideanSpace ℝ (Fin n))
        (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      IsSelfAdjoint H → ‖H‖ ≤ LH →
        |penalty hm f g c ξs ε (quarticGamma ε) α π (x + d)
            - model hm f g c ξs ε (quarticGamma ε) α π x H d| ≤ K * ‖d‖ ^ 2 := by sorry

end SmoothCCP.PenaltyModel
