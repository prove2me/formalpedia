-- Prove2me | Theorems.Thm_UnivAccel_ball_answer_continuity
-- name    : UnivAccel.ball_answer_continuity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:40.194957+00:00
-- url     : https://prove2.me/theorems/8433d912-4031-4a23-80e9-e69136d3f178
-- title:
--   §4.2 Computing $h$ — the ball oracle's answer moves continuously with the centre
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be differentiable and $\mu$-strongly convex with $\mu > 0$, and let $r > 0$. Take two centres $c$ and $c' = c + d$ with answers $y = \mathrm{Ball}^f_r(c)$ and $y' = \mathrm{Ball}^f_r(c')$, and let $M$ bound $\|\nabla f\|$ on a compact convex set containing $y$, $y'$, $y + d$ and $y' - d$. Then
--   $$
--   \mu\|y' - y - d\|^2 \le \big[f(y' - d) - f(y')\big] + \big[f(y + d) - f(y)\big] \le 2M\|d\|,
--   $$
--   hence
--   $$
--   \|y' - y\| \le \|d\| + \sqrt{2M\|d\|/\mu}.
--   $$
--
--   So the answer moves continuously with the centre, which is what bisection on the step duration needs.
--
--   Differences from the source: none.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §4.2 "Computing h", p.14

import Mathlib
import Definitions.Def_UnivAccel_IsBallOracle

namespace UnivAccel

/-- §4.2 "Computing h", p.14 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)): the ball oracle's answer moves continuously with the
centre. Let `f` be differentiable and `μ`-strongly convex, `μ > 0`, `r > 0`; take two centres `c`
and `c' = c + d` with answers `y = Ball^f_r(c)`, `y' = Ball^f_r(c')`, and let `M` bound `‖∇f‖` on a
compact convex set containing `y`, `y'`, `y + d` and `y' − d`. Then
`μ‖y' − y − d‖² ≤ [f(y' − d) − f(y')] + [f(y + d) − f(y)] ≤ 2M‖d‖`, hence
`‖y' − y‖ ≤ ‖d‖ + √(2M‖d‖/μ)`. -/
theorem ball_answer_continuity {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ r M : ℝ)
    (c d y y' : EuclideanSpace ℝ (Fin n)) (S : Set (EuclideanSpace ℝ (Fin n)))
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ μ f) (hμ : 0 < μ) (hr : 0 < r)
    (hy : IsBallMin f c r y) (hy' : IsBallMin f (c + d) r y')
    (hScvx : Convex ℝ S) (hScpt : IsCompact S)
    (hyS : y ∈ S) (hy'S : y' ∈ S) (hydS : y + d ∈ S) (hy'dS : y' - d ∈ S)
    (hM : ∀ u ∈ S, ‖gradient f u‖ ≤ M) :
    μ * ‖y' - y - d‖ ^ 2 ≤ (f (y' - d) - f y') + (f (y + d) - f y) ∧
    (f (y' - d) - f y') + (f (y + d) - f y) ≤ 2 * M * ‖d‖ ∧
    ‖y' - y‖ ≤ ‖d‖ + Real.sqrt (2 * M * ‖d‖ / μ) := by sorry

end UnivAccel
