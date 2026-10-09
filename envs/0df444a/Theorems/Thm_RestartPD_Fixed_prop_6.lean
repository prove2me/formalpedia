-- Prove2me | Theorems.Thm_RestartPD_Fixed_prop_6
-- name    : RestartPD.Fixed.prop_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:31.490101+00:00
-- url     : https://prove2.me/theorems/a7157b51-824f-4a56-b8aa-f51b0c6d1cc0
-- title:
--   Proposition 6, p. 11 — the primal-dual gap at z is zero iff ρ_r(z) = 0
-- statement:
--   Let $X$, $Y$ be convex, let $L$ be convex in $x$ on $X$ and concave in $y$ on $Y$, and let $\|\cdot\|$ be any semi-norm. For every $z \in Z$ and every $r \in [0, \infty)$,
--   $$\sup_{\hat z \in Z} \{L(x, \hat y) - L(\hat x, y)\} = 0 \iff \rho_r(z) = 0.$$
--
--   Since a point has zero primal-dual gap exactly when it solves (1), the normalized duality gap at any radius detects solutions.
--
--   **Formalization Note** Both sides are extended reals. Only the convexity hypotheses of (1) are assumed; $z \in Z$ is assumed, as on the page, where $\rho_r$ is evaluated at feasible points.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, p. 11, Proposition 6

import Mathlib
import Definitions.Def_RestartPD_Fixed_Problem

namespace RestartPD.Fixed

/-- Proposition 6, p. 11: for `z ∈ Z` and `r ∈ [0, ∞)`, the primal-dual gap (3) at `z` is zero
if and only if `ρ_r(z) = 0`. -/
theorem prop_6 {n m : ℕ} (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (hX : Convex ℝ X) (hY : Convex ℝ Y)
    (hLx : ∀ y ∈ Y, ConvexOn ℝ X (fun x => L x y))
    (hLy : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => L x y))
    (p : Seminorm ℝ (E n m)) (z : E n m) (hz : z ∈ X ×ˢ Y) (r : ℝ) (hr : 0 ≤ r) :
    pdGap L X Y z = 0 ↔ rho L X Y p r z = 0 := by sorry

end RestartPD.Fixed
