-- Prove2me | Theorems.Thm_PenaltyLag_Asymptotic_corollary_3_3
-- name    : PenaltyLag.Asymptotic.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:31.436306+00:00
-- url     : https://prove2.me/theorems/eb191ade-e58d-461c-89fc-33854ca2e8e3
-- title:
--   Corollary 3.3 — the quadratic sandwich (3.16) for $g_r$
-- statement:
--   Throughout, $X$ is a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m : X \to \mathbb R$ are convex (the paper's standing assumption of §3, p. 358). Let $r > 0$ and suppose $g_r$ is not identically $-\infty$. Then for all $y, y' \in \mathbb R^m$,
--   $$
--   g_r(y) + (y' - y) \cdot \nabla g_r(y) \;\ge\; g_r(y') \;\ge\; g_r(y) + (y' - y) \cdot \nabla g_r(y) - \frac{1}{4r}|y' - y|^2. \tag{3.16}
--   $$
--
--   The upper bound is concavity; the lower bound says that $g_r$ is never more curved than the quadratic $-\frac{1}{4r}|\cdot|^2$, the estimate that drives the convergence argument of §4.
--
--   **Formalization Note** $r > 0$ is the setting of Theorem 3.2, implicit in the corollary. "Unless identically $-\infty$" is the hypothesis that $g_r(z) \ne -\infty$ for some $z$; under it $g_r$ is finite (Theorem 3.2), and the inequalities are stated for its real coercion `grR` and its gradient. The paper's functions $f_i : X \to \mathbb R$ are total functions $E \to \mathbb R$ convex on $X$, and only their values on $X$ enter; constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$), and $f_0$ is a separate argument; the standing assumption (p. 358: $X$ nonempty convex, $f_i$ convex) is a hypothesis even where the statement does not repeat it.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 361, Corollary 3.3, (3.16)

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

open Filter Topology

namespace PenaltyLag.Asymptotic

/-- Corollary 3.3 (p. 361): for r > 0, unless g_r ≡ −∞, the quadratic sandwich (3.16). -/
theorem corollary_3_3 {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (hgr : ∃ z : Mult m, gr X f₀ f r z ≠ ⊥) (y y' : Mult m) :
    grR X f₀ f r y + inner ℝ (y' - y) (gradient (grR X f₀ f r) y) ≥ grR X f₀ f r y' ∧
    grR X f₀ f r y' ≥
      grR X f₀ f r y + inner ℝ (y' - y) (gradient (grR X f₀ f r) y) - (1 / (4 * r)) * ‖y' - y‖ ^ 2 := by sorry

end PenaltyLag.Asymptotic
