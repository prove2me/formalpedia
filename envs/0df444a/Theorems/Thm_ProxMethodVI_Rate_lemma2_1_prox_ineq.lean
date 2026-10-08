-- Prove2me | Theorems.Thm_ProxMethodVI_Rate_lemma2_1_prox_ineq
-- name    : ProxMethodVI.Rate.lemma2_1_prox_ineq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:57.100609+00:00
-- url     : https://prove2.me/theorems/33cf9309-0096-4b73-b119-f80e62aefc4e
-- title:
--   Lemma 2.1 (2.5), p. 232 — H_u(P_z(ξ)) − H_u(z) ≤ ⟨ξ, u − P_z(ξ)⟩ + [ω(z) + ⟨ω′(z), P_z(ξ) − z⟩ − ω(P_z(ξ))], and the bracket is ≤ 0
-- statement:
--   Let $Z$ be a nonempty convex compact subset of a finite-dimensional normed space $E$, and let $\omega$ be continuously differentiable on $Z$ and $\alpha$-strongly convex in the sense of (2.2). Let $\Omega$ be the Legendre transform of $\omega|_Z$, let $H_u(z)=\Omega(\omega'(z))-\langle\omega'(z),u\rangle$, and let $P_z(\xi)$ be the prox-mapping. Let $z\in Z$, let $\xi$ be a dual vector, and let $v=P_z(\xi)$. Then for every $u\in Z$,
--   $$H_u(v)-H_u(z)\le\langle\xi,u-v\rangle+\big[\omega(z)+\langle\omega'(z),v-z\rangle-\omega(v)\big],$$
--   and the bracket satisfies
--   $$\omega(z)+\langle\omega'(z),v-z\rangle-\omega(v)\le0.$$
--
--   This is the basic one-step inequality of the prox-method. $H_u$ plays the role of a potential, and summing (2.5) along a run gives the ergodic error bound of Proposition 2.2.
--
--   **Formalization Note.** "$v=P_z(\xi)$" is the relation that $v\in Z$ minimizes $\omega(y)+\langle\xi-\omega'(z),y\rangle$ over $Z$. Dual vectors are continuous linear functionals and $\langle\xi,x\rangle$ is $\xi(x)$; this is equivalent to the paper's inner-product setting.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t), SIAM J. Optim. 15(1) (2004), p. 232, Lemma 2.1, (2.5)

import Mathlib
import Definitions.Def_ProxMethodVI_Rate_Setting

namespace ProxMethodVI.Rate

theorem lemma2_1_prox_ineq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (z : E) (hz : z ∈ Z) (ξ : E →L[ℝ] ℝ) (v : E) (hv : IsProxPt Z ω ω' z ξ v)
    (u : E) (hu : u ∈ Z) :
    Hfun Z ω ω' u v - Hfun Z ω ω' u z ≤ ξ (u - v) + (ω z + ω' z (v - z) - ω v) ∧
      ω z + ω' z (v - z) - ω v ≤ 0 := by sorry

end ProxMethodVI.Rate
