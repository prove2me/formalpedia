-- Prove2me | Theorems.Thm_ProxMethodVI_Rate_theorem3_2_second_inner_step
-- name    : ProxMethodVI.Rate.theorem3_2_second_inner_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:56.71598+00:00
-- url     : https://prove2.me/theorems/a38a5a59-86f5-4ea7-a2cd-e7e4a273377f
-- title:
--   Proof of Theorem 3.2, p. 239 — with γ = α/(√2L), the second inner iterate w_{t,2} always passes (3.4)
-- statement:
--   Let $Z$ be a nonempty convex compact subset of a finite-dimensional normed space $E$, let $F$ satisfy (2.1) with a constant $L>0$ (Lipschitz from $\|\cdot\|$ to $\|\cdot\|_*$ and monotone on $Z$), and let $\omega$ be continuously differentiable on $Z$ and $\alpha$-strongly convex in the sense of (2.2). Let $\gamma=\alpha/(\sqrt2L)$ as in (3.2). Let $z\in Z$, let $w_1=P_z(\gamma F(z))$ and $w_2=P_z(\gamma F(w_1))$. Then
--   $$\langle\gamma F(w_1),w_1-w_2\rangle+\omega(z)+\langle\omega'(z),w_2-z\rangle-\omega(w_2)\le0,$$
--   that is, the test (3.4) is met at the second inner iteration $s=2$.
--
--   This is the display of the proof of Theorem 3.2. It is what makes every step of the basic implementation cost at most two evaluations of $F$ and two prox problems.
--
--   **Formalization Note.** The statement is unconditional: it does not assume that (3.4) fails at $s=1$, because the proof's display never uses that failure. It is therefore slightly stronger than the sentence "if (3.4) is not met with $s_t=1$, it is met with $s_t=2$". $L>0$ is needed for (3.2) to make sense. Prox points are minimizers over $Z$.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t), SIAM J. Optim. 15(1) (2004), p. 239, proof of Theorem 3.2, display; (3.2)–(3.4)

import Mathlib
import Definitions.Def_ProxMethodVI_Rate_Setting

namespace ProxMethodVI.Rate

theorem theorem3_2_second_inner_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (F : E → E →L[ℝ] ℝ) (L : ℝ) (hL : 0 < L) (hLip : IsLipschitzOnWRT Z F L)
    (hmono : IsMonotoneOnWRT Z F)
    (z : E) (hz : z ∈ Z) (w₁ : E) (hw₁ : IsProxPt Z ω ω' z ((α / (Real.sqrt 2 * L)) • F z) w₁)
    (zp : E) (hzp : IsProxPt Z ω ω' z ((α / (Real.sqrt 2 * L)) • F w₁) zp) :
    test34 (α / (Real.sqrt 2 * L)) F ω ω' z w₁ zp := by sorry

end ProxMethodVI.Rate
