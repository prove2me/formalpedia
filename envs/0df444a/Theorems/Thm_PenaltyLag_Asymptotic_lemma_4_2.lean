-- Prove2me | Theorems.Thm_PenaltyLag_Asymptotic_lemma_4_2
-- name    : PenaltyLag.Asymptotic.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:47.121343+00:00
-- url     : https://prove2.me/theorems/5ef3a12d-a5c0-4d5d-967a-dbd2532462d6
-- title:
--   Lemma 4.2 — $r|\nabla g_r(y)|^2 \le \sup g_r - g_r(y)$
-- statement:
--   Throughout, $X$ is a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m : X \to \mathbb R$ are convex (the paper's standing assumption of §3, p. 358). Let $r > 0$ and suppose $g_r$ is not identically $-\infty$. Then for every $y \in \mathbb R^m$,
--   $$
--   r\,|\nabla g_r(y)|^2 \;\le\; \Big(\sup_{y'} g_r(y')\Big) - g_r(y).
--   $$
--
--   Along a maximizing sequence the right side tends to $0$, so the dual gradients tend to $0$.
--
--   **Formalization Note** The paper states the lemma for the terms $y^k$ of a sequence; the sequence plays no role, and it is stated for every $y$. The scan loses the minus sign: the line prints "(sup $g_r$) $g_r(y_k)$", read as $(\sup g_r) - g_r(y^k)$, and $y_k$ is $y^k$. The right side is computed in `EReal` ($\sup g_r$ may be $+\infty$, in which case the inequality is trivial, as in the paper); $g_r(y)$ is finite under the hypothesis. The paper's functions $f_i : X \to \mathbb R$ are total functions $E \to \mathbb R$ convex on $X$, and only their values on $X$ enter; constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$), and $f_0$ is a separate argument; the standing assumption (p. 358: $X$ nonempty convex, $f_i$ convex) is a hypothesis even where the statement does not repeat it.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 365, Lemma 4.2

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

open Filter Topology

namespace PenaltyLag.Asymptotic

/-- Lemma 4.2 (p. 365): r|∇g_r(y)|² ≤ (sup g_r) − g_r(y), for every y, when r > 0 and g_r ≢ −∞. -/
theorem lemma_4_2 {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) (hgr : ∃ z : Mult m, gr X f₀ f r z ≠ ⊥) (y : Mult m) :
    ((r * ‖gradient (grR X f₀ f r) y‖ ^ 2 : ℝ) : EReal)
      ≤ (⨆ y' : Mult m, gr X f₀ f r y') - gr X f₀ f r y := by sorry

end PenaltyLag.Asymptotic
