-- Prove2me | Theorems.Thm_ProxMethodVI_Rate_lemma3_1_c
-- name    : ProxMethodVI.Rate.lemma3_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:59.138655+00:00
-- url     : https://prove2.me/theorems/0376233c-db86-4868-82a2-49632d39b9dc
-- title:
--   Lemma 3.1 (3.7.c), p. 238 — δ ≤ ε
-- statement:
--   Let $Z$ be a nonempty convex compact subset of a finite-dimensional normed space $E$, and let $\omega$ be continuously differentiable on $Z$ and $\alpha$-strongly convex in the sense of (2.2). Let a nonempty set $U\subseteq Z$ be convex and closed, let $z\in Z$, let $\xi,\eta$ be dual vectors, let $\gamma>0$, and let $w,z_+$ be the points (3.6) (minimizers over $U$). Then
--   $$\underbrace{\langle\gamma\eta,w-z_+\rangle+\big[\omega(z)+\langle\omega'(z),z_+-z\rangle-\omega(z_+)\big]}_{\delta}\le\underbrace{\langle\gamma(\eta-\xi),w-z_+\rangle+\big[\omega(z)+\langle\omega'(z),w-z\rangle+\langle\omega'(w),z_+-w\rangle-\omega(z_+)\big]}_{\epsilon}.$$
--
--   This is part (c) of Lemma 3.1. It replaces the left-hand side $\delta$ of the test (3.4) by a quantity $\epsilon$ in which the two prox steps are decoupled.
--
--   **Formalization Note.** $\delta$ and $\epsilon$ are written out in full. The lemma's "for all $u\in U$" binds nothing in part (c) and is omitted.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t), SIAM J. Optim. 15(1) (2004), pp. 237–238, Lemma 3.1, (3.6), (3.7.c)

import Mathlib
import Definitions.Def_ProxMethodVI_Rate_Setting

namespace ProxMethodVI.Rate

theorem lemma3_1_c {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (U : Set E) (hUZ : U ⊆ Z) (hUne : U.Nonempty) (hUc : Convex ℝ U) (hUcl : IsClosed U)
    (z : E) (hz : z ∈ Z) (ξ η : E →L[ℝ] ℝ) (γ : ℝ) (hγ : 0 < γ)
    (w : E) (hw : IsProxPt U ω ω' z (γ • ξ) w)
    (zp : E) (hzp : IsProxPt U ω ω' z (γ • η) zp) :
    γ * η (w - zp) + (ω z + ω' z (zp - z) - ω zp)
      ≤ γ * (η - ξ) (w - zp) + (ω z + ω' z (w - z) + ω' w (zp - w) - ω zp) := by sorry

end ProxMethodVI.Rate
