-- Prove2me | Theorems.Thm_ProxMethodVI_Rate_lemma3_1_a_prox_lipschitz
-- name    : ProxMethodVI.Rate.lemma3_1_a_prox_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:08.745981+00:00
-- url     : https://prove2.me/theorems/8a5aacb0-cfed-46c6-a1c9-7955c27efdf3
-- title:
--   Lemma 3.1 (3.7.a), p. 238 — ‖w − z₊‖ ≤ α⁻¹γ‖ξ − η‖_*
-- statement:
--   Let $Z$ be a nonempty convex compact subset of a finite-dimensional normed space $E$, and let $\omega$ be continuously differentiable on $Z$ and $\alpha$-strongly convex in the sense of (2.2). Let a nonempty set $U\subseteq Z$ be convex and closed, let $z\in Z$, let $\xi,\eta$ be dual vectors and let $\gamma>0$. Consider the points
--   $$w=\operatorname*{argmin}_{y\in U}\big[\langle\gamma\xi-\omega'(z),y\rangle+\omega(y)\big],\qquad z_+=\operatorname*{argmin}_{y\in U}\big[\langle\gamma\eta-\omega'(z),y\rangle+\omega(y)\big].\tag{3.6}$$
--   Then
--   $$\|w-z_+\|\le\alpha^{-1}\gamma\|\xi-\eta\|_*.$$
--
--   This is part (a) of Lemma 3.1, the key lemma of the two-step analysis. It is used in (3.7.d) to bound the inner-product term.
--
--   **Formalization Note.** $w$ and $z_+$ are any minimizers of the two problems (3.6). The lemma's "for all $u\in U$" binds nothing in part (a) and is omitted. $\|\xi-\eta\|_*$ is the operator norm.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t), SIAM J. Optim. 15(1) (2004), pp. 237–238, Lemma 3.1, (3.6), (3.7.a)

import Mathlib
import Definitions.Def_ProxMethodVI_Rate_Setting

namespace ProxMethodVI.Rate

theorem lemma3_1_a_prox_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (U : Set E) (hUZ : U ⊆ Z) (hUne : U.Nonempty) (hUc : Convex ℝ U) (hUcl : IsClosed U)
    (z : E) (hz : z ∈ Z) (ξ η : E →L[ℝ] ℝ) (γ : ℝ) (hγ : 0 < γ)
    (w : E) (hw : IsProxPt U ω ω' z (γ • ξ) w)
    (zp : E) (hzp : IsProxPt U ω ω' z (γ • η) zp) :
    ‖w - zp‖ ≤ α⁻¹ * γ * ‖ξ - η‖ := by sorry

end ProxMethodVI.Rate
