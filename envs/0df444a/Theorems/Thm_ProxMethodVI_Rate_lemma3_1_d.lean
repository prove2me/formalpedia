-- Prove2me | Theorems.Thm_ProxMethodVI_Rate_lemma3_1_d
-- name    : ProxMethodVI.Rate.lemma3_1_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:12.650126+00:00
-- url     : https://prove2.me/theorems/6a80e366-f002-4189-b8fc-ff4eb8e61291
-- title:
--   Lemma 3.1 (3.7.d), p. 238 — ε ≤ α⁻¹γ²‖ξ − η‖²_* − (α/2)[‖w − z‖² + ‖w − z₊‖²]
-- statement:
--   Let $Z$ be a nonempty convex compact subset of a finite-dimensional normed space $(E,\|\cdot\|)$, and let $\omega$ be continuously differentiable on $Z$ and $\alpha$-strongly convex in the sense of (2.2). Let a nonempty set $U\subseteq Z$ be convex and closed, let $z\in Z$, let $\xi,\eta$ be dual vectors, let $\gamma>0$, and let $w,z_+$ be the points (3.6) (minimizers over $U$). Then
--   $$\underbrace{\langle\gamma(\eta-\xi),w-z_+\rangle+\big[\omega(z)+\langle\omega'(z),w-z\rangle+\langle\omega'(w),z_+-w\rangle-\omega(z_+)\big]}_{\epsilon}\le\alpha^{-1}\gamma^2\|\xi-\eta\|_*^2-\frac{\alpha}{2}\big[\|w-z\|^2+\|w-z_+\|^2\big].$$
--
--   This is part (d) of Lemma 3.1. Together with (3.7.c) it bounds the left-hand side of the test (3.4) at the second inner iteration, and it carries the constant that makes the stepsize $\gamma=\alpha/(\sqrt2L)$ work in Theorem 3.2.
--
--   **Formalization Note.** $\epsilon$ is written out in full. $\|\xi-\eta\|_*$ is the operator norm. Strong convexity is assumed only in the monotonicity form (2.2); its function-value form is not a hypothesis.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t), SIAM J. Optim. 15(1) (2004), pp. 237–238, Lemma 3.1, (3.6), (3.7.d)

import Mathlib
import Definitions.Def_ProxMethodVI_Rate_Setting

namespace ProxMethodVI.Rate

theorem lemma3_1_d {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (U : Set E) (hUZ : U ⊆ Z) (hUne : U.Nonempty) (hUc : Convex ℝ U) (hUcl : IsClosed U)
    (z : E) (hz : z ∈ Z) (ξ η : E →L[ℝ] ℝ) (γ : ℝ) (hγ : 0 < γ)
    (w : E) (hw : IsProxPt U ω ω' z (γ • ξ) w)
    (zp : E) (hzp : IsProxPt U ω ω' z (γ • η) zp) :
    γ * (η - ξ) (w - zp) + (ω z + ω' z (w - z) + ω' w (zp - w) - ω zp)
      ≤ α⁻¹ * γ ^ 2 * ‖ξ - η‖ ^ 2 - α / 2 * (‖w - z‖ ^ 2 + ‖w - zp‖ ^ 2) := by sorry

end ProxMethodVI.Rate
