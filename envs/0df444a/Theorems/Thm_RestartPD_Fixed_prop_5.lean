-- Prove2me | Theorems.Thm_RestartPD_Fixed_prop_5
-- name    : RestartPD.Fixed.prop_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:09.775863+00:00
-- url     : https://prove2.me/theorems/8fcb1182-21c4-4c2d-bdca-3adbc6256980
-- title:
--   Proposition 5, p. 11 — ρ_r(z) is non-increasing in r ∈ [0, ∞)
-- statement:
--   Let $X$, $Y$ be convex, let $L$ be convex in $x$ on $X$ and concave in $y$ on $Y$, and let $\|\cdot\|$ be any semi-norm. For every $z \in Z = X \times Y$, the normalized duality gap $r \mapsto \rho_r(z)$ is non-increasing on $[0, \infty)$:
--   $$0 \le r_1 \le r_2 \implies \rho_{r_2}(z) \le \rho_{r_1}(z).$$
--
--   Monotonicity in the radius makes $\rho_0(z)$ an honest limit and lets a bound on $\rho_r$ at one radius control all smaller radii.
--
--   **Formalization Note** Values are in $[-\infty, +\infty]$. Only the convexity hypotheses of (1) are assumed. The page says "for any fixed $z$"; $z \in Z$ is assumed, since for $z \notin Z$ the ball $W_r(z)$ may be empty for small $r$ and $\rho_r(z) = -\infty$.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 11, Proposition 5

import Mathlib
import Definitions.Def_RestartPD_Fixed_Problem

namespace RestartPD.Fixed

/-- Proposition 5, p. 11: for a fixed `z ∈ Z`, `r ↦ ρ_r(z)` is non-increasing on `[0, ∞)`. -/
theorem prop_5 {n m : ℕ} (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hLx : ∀ y ∈ Y, ConvexOn ℝ X (fun x => L x y))
    (hLy : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => L x y))
    (p : Seminorm ℝ (E n m)) (z : E n m) (hz : z ∈ X ×ˢ Y) :
    AntitoneOn (fun r : ℝ => rho L X Y p r z) (Set.Ici 0) := by sorry

end RestartPD.Fixed
