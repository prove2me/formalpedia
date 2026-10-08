-- Prove2me | Theorems.Thm_PenaltyLag_Asymptotic_asymp_value_eq_dual_value
-- name    : PenaltyLag.Asymptotic.asymp_value_eq_dual_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:28.904608+00:00
-- url     : https://prove2.me/theorems/afc1b652-19c5-4c4f-ac7c-9480c46c16d4
-- title:
--   §4, after (4.5) — asymptotic optimal value in (P) = dual optimal value
-- statement:
--   Throughout, $X$ is a nonempty convex subset of a real vector space $E$ and $f_0, f_1, \dots, f_m : X \to \mathbb R$ are convex (the paper's standing assumption of §3, p. 358). Suppose the dual optimal value $\sup_y g_0(y)$ is not $-\infty$, or there exists at least one asymptotically feasible sequence for (P). Then
--   $$
--   \text{asymptotic optimal value in (P)} \;=\; \sup_{y \in \mathbb R^m} g_0(y).
--   $$
--
--   The paper cites this as well known (its references [7, 11, 19]); it is the zero-duality-gap theorem in its asymptotic form, with no constraint qualification, and it is the fact that turns the dual limit (4.13) into asymptotic minimality in Theorem 4.1.
--
--   **Formalization Note** Both values are in `EReal`; the asymptotic optimal value is $+\infty$ when there is no asymptotically feasible sequence. No topology on $E$ is assumed; asymptotic feasibility only involves the real numbers $f_i(x^k)$. The dual optimal value is $\sup g_0$, which equals $\sup g_r$ for every $r > 0$ by Theorem 3.2. The paper's functions $f_i : X \to \mathbb R$ are total functions $E \to \mathbb R$ convex on $X$, and only their values on $X$ enter; constraint indices are `Fin m` (0-based, the paper's $1, \dots, m$), and $f_0$ is a separate argument; the standing assumption (p. 358: $X$ nonempty convex, $f_i$ convex) is a hypothesis even where the statement does not repeat it.
-- source:
--   Rockafellar, A Dual Approach to Solving Nonlinear Programming Problems by Unconstrained Optimization, Math. Programming 5 (1973), p. 364, §4, after (4.5)

import Mathlib
import Definitions.Def_PenaltyLag_Asymptotic_Basic

open Filter Topology

namespace PenaltyLag.Asymptotic

/-- §4, after (4.5) (p. 364): the asymptotic optimal value in (P) equals the dual optimal value if
the latter is not −∞, or if asymptotically feasible sequences exist. -/
theorem asymp_value_eq_dual_value {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (X : Set E) (hX : Convex ℝ X) (hXne : X.Nonempty)
    (f₀ : E → ℝ) (f : Fin m → E → ℝ) (hf₀ : ConvexOn ℝ X f₀) (hf : ∀ i, ConvexOn ℝ X (f i))
    (h : dualValue X f₀ f ≠ ⊥ ∨ ∃ x : ℕ → E, IsAsympFeasible X f x) :
    asympValue X f₀ f = dualValue X f₀ f := by sorry

end PenaltyLag.Asymptotic
