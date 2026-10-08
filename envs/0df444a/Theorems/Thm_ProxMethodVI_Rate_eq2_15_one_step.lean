-- Prove2me | Theorems.Thm_ProxMethodVI_Rate_eq2_15_one_step
-- name    : ProxMethodVI.Rate.eq2_15_one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:06.409965+00:00
-- url     : https://prove2.me/theorems/26e755fd-c503-4fc0-b1e6-5393f8974f9c
-- title:
--   (2.15), proof of Proposition 2.2, p. 235 — ⟨γ_tF(w_t), w_t − u⟩ ≤ H_u(z_{t−1}) − H_u(z_t) + ε_t
-- statement:
--   Let $Z$ be a nonempty convex compact subset of a finite-dimensional normed space $E$, let $\omega$ be continuously differentiable on $Z$ and $\alpha$-strongly convex in the sense of (2.2), and let $H_u$ be as in (2.3). Consider a run $(z_t)$, $(w_t)$ of the relaxed conceptual prox-method with stepsizes $\gamma_t>0$ and tolerances $\epsilon_t$: $z_0\in Z$, $w_t\in Z$, $z_t=P_{z_{t-1}}(\gamma_tF(w_t))$, and condition (2.11) holds at every step $t\ge1$. Then for every step $t\ge1$ and every $u\in Z$,
--   $$\langle\gamma_tF(w_t),w_t-u\rangle\le H_u(z_{t-1})-H_u(z_t)+\epsilon_t.$$
--
--   This one-step estimate telescopes over $t=1,\dots,N$ to give (2.16) and then the ergodic bound (2.13).
--
--   **Formalization Note.** No property of $F$ is used, so $F$ is an arbitrary map (the section's standing assumption (2.1) is dropped here, which is a generalization). In Lean the step $t\ge1$ of the paper is the index `t + 1`, `t : ℕ`. The termination test (2.8) is not part of the run.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t), SIAM J. Optim. 15(1) (2004), p. 235, proof of Proposition 2.2, (2.15)

import Mathlib
import Definitions.Def_ProxMethodVI_Rate_Setting

namespace ProxMethodVI.Rate

theorem eq2_15_one_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Z : Set E) (hZc : Convex ℝ Z) (hZk : IsCompact Z) (hZne : Z.Nonempty)
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) (α : ℝ) (hω : IsStrongDGF Z ω ω' α)
    (F : E → E →L[ℝ] ℝ) (γ ε : ℕ → ℝ) (z w : ℕ → E)
    (hrun : IsRelaxedRun Z F ω ω' γ ε z w) (t : ℕ) (u : E) (hu : u ∈ Z) :
    γ (t + 1) * F (w (t + 1)) (w (t + 1) - u)
      ≤ Hfun Z ω ω' u (z t) - Hfun Z ω ω' u (z (t + 1)) + ε (t + 1) := by sorry

end ProxMethodVI.Rate
