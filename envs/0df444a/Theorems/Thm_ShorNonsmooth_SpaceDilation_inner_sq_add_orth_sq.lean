-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_inner_sq_add_orth_sq
-- name    : ShorNonsmooth.SpaceDilation.inner_sq_add_orth_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T20:23:55.994988+00:00
-- url     : https://prove2.me/theorems/1574ce4f-0b4d-4a2c-9a51-bc6a6ea8b2b7
-- title:
--   Pythagoras for an orthogonal decomposition $u = c\,\xi + w$ with $\langle w,\xi\rangle = 0$ and $\|\xi\| = 1$ (Shor 1985, p. 56 step)
-- statement:
--   In an inner-product space, if a vector $u$ decomposes as $u = c\,\xi + w$ with $w$ orthogonal to $\xi$ and $\xi$ a unit vector, then $\|u\|^2 = c^2 + \|w\|^2$.
--
--   This is the ordinary Pythagorean identity in inner-product form: $\|c\,\xi + w\|^2 = c^2\|\xi\|^2 + 2c\langle\xi,w\rangle + \|w\|^2 = c^2 + \|w\|^2$. It is used in the proof of Theorem 3.3 (Shor 1985, pp. 56-57) to split $u_k = \gamma\xi_k + w_k$ along the normalized selection direction $\xi_k$, so that the one-step estimate for $\|u_{k+1}\|$ reduces to a scalar comparison.
-- source:
--   Shor, Extensions of Subgradient Methods for Minimization (1985), p. 56: the decomposition of $u_k$ into its component along $\xi_k$ and the orthogonal remainder.

import Mathlib

namespace ShorNonsmooth.SpaceDilation

/-- If `u = c • ξ + w` and `⟪w, ξ⟫ = 0` with `‖ξ‖ = 1`, then `‖u‖ ^ 2 = c ^ 2 + ‖w‖ ^ 2`. -/
theorem inner_sq_add_orth_sq {n : ℕ} (u ξ w : EuclideanSpace ℝ (Fin n))
    (c : ℝ) (hξ : ‖ξ‖ = 1) (hdecomp : u = c • ξ + w) (horth : inner ℝ w ξ = 0) :
    ‖u‖ ^ 2 = c ^ 2 + ‖w‖ ^ 2 := by
  sorry

end ShorNonsmooth.SpaceDilation
