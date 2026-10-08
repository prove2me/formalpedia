-- Prove2me | Theorems.Thm_PenaltyLag_Asymptotic_lemma_4_3
-- name    : PenaltyLag.Asymptotic.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:22.935788+00:00
-- url     : https://prove2.me/theorems/e66c2ef4-bccb-4042-b9fc-21f334add6c0
-- title:
--   Lemma 4.3 — (4.7) implies $r|\nabla_y L_r(x,y) - \nabla g_r(y)|^2 \le \alpha$
-- statement:
--   Throughout, $X$ is a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m : X \to \mathbb R$ are convex (the paper's standing assumption of §3, p. 358). Let $r > 0$, $x \in X$, $y \in \mathbb R^m$ and $\alpha \in \mathbb R$, and suppose $x$ is an $\alpha$-minimizer of $L_r(\cdot, y)$:
--   $$
--   L_r(x, y) - g_r(y) \le \alpha. \tag{4.7}
--   $$
--   Then
--   $$
--   r\,\big|\nabla_y L_r(x, y) - \nabla g_r(y)\big|^2 \le \alpha.
--   $$
--
--   So the easily computed gradient $\nabla_y L_r(x, y)$ at an approximate minimizer is close to the true dual gradient.
--
--   **Formalization Note** The paper states the lemma for the pairs $(x^k, y^k)$, $\alpha_k$ of Theorem 4.1; it is stated here for one pair. (4.7) is written $L_r(x, y) \le g_r(y) + \alpha$ in `EReal`, which is equivalent since $L_r(x, y)$ is real and $g_r(y) < +\infty$, and avoids `EReal` subtraction; it forces $g_r(y) > -\infty$, so $g_r$ is finite and $\nabla g_r$ (the gradient of the real coercion `grR`) is meaningful. The paper's functions $f_i : X \to \mathbb R$ are total functions $E \to \mathbb R$ convex on $X$, and only their values on $X$ enter; constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$), and $f_0$ is a separate argument; the standing assumption (p. 358: $X$ nonempty convex, $f_i$ convex) is a hypothesis even where the statement does not repeat it.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), pp. 365–366, Lemma 4.3, (4.7), (4.8)

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

open Filter Topology

namespace PenaltyLag.Asymptotic

/-- Lemma 4.3 (pp. 365–366): if x ∈ X satisfies (4.7) at y with tolerance α, i.e.
L_r(x, y) ≤ g_r(y) + α, then r|∇_y L_r(x, y) − ∇g_r(y)|² ≤ α. -/
theorem lemma_4_3 {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (x : E) (hx : x ∈ X) (y : Mult m) (α : ℝ)
    (h47 : (Lr f₀ f r x y : EReal) ≤ gr X f₀ f r y + (α : EReal)) :
    r * ‖gradient (fun y' : Mult m => Lr f₀ f r x y') y - gradient (grR X f₀ f r) y‖ ^ 2 ≤ α := by sorry

end PenaltyLag.Asymptotic
