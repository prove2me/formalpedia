-- Prove2me | Theorems.Thm_PenaltyLag_Asymptotic_theorem_3_2_same_dual
-- name    : PenaltyLag.Asymptotic.theorem_3_2_same_dual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:33.908453+00:00
-- url     : https://prove2.me/theorems/cf8654bb-e9bb-48b3-82be-cf2ac0a41f10
-- title:
--   Theorem 3.2 (second sentence) — $(D_r)$ and $(D_0)$ have the same supremum and the same optimal solutions
-- statement:
--   Throughout, $X$ is a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m : X \to \mathbb R$ are convex (the paper's standing assumption of §3, p. 358). For every $r > 0$,
--   $$
--   \sup_{y \in \mathbb R^m} g_r(y) = \sup_{y \in \mathbb R^m} g_0(y),
--   $$
--   and a vector $\bar y$ is an optimal solution of $(D_r)$ if and only if it is an optimal solution of the ordinary dual $(D_0)$. Here $\bar y$ is an optimal solution of a dual problem when it attains the supremum and that supremum is not $-\infty$.
--
--   Because of this the paper speaks simply of dual optimal solutions and the dual optimal value, independent of $r$.
--
--   **Formalization Note** The paper's convention (p. 361) that dual optimal solutions do not exist when the functions $g_r$ are identically $-\infty$ is encoded by the clause $g(\bar y) \ne -\infty$ on both sides. Suprema are taken in `EReal`. The paper's functions $f_i : X \to \mathbb R$ are total functions $E \to \mathbb R$ convex on $X$, and only their values on $X$ enter; constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$), and $f_0$ is a separate argument; the standing assumption (p. 358: $X$ nonempty convex, $f_i$ convex) is a hypothesis even where the statement does not repeat it.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 359, Theorem 3.2 (second sentence); convention p. 361

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

open Filter Topology

namespace PenaltyLag.Asymptotic

/-- Theorem 3.2, second sentence (p. 359): for r > 0, (D_r) and (D₀) have the same supremum and
the same optimal solutions (an optimal solution is a point attaining a supremum that is not −∞,
the paper's convention on p. 361). -/
theorem theorem_3_2_same_dual {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (r : ℝ) (hr : 0 < r) :
    (⨆ y : Mult m, gr X f₀ f r y) = (⨆ y : Mult m, g0 X f₀ f y) ∧
    ∀ ybar : Mult m,
      (gr X f₀ f r ybar ≠ ⊥ ∧ gr X f₀ f r ybar = ⨆ y : Mult m, gr X f₀ f r y) ↔
      (g0 X f₀ f ybar ≠ ⊥ ∧ g0 X f₀ f ybar = ⨆ y : Mult m, g0 X f₀ f y) := by sorry

end PenaltyLag.Asymptotic
