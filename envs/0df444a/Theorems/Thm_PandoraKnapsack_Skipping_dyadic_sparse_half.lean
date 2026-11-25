-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_dyadic_sparse_half
-- name    : PandoraKnapsack.Skipping.dyadic_sparse_half
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:13:37.895698+00:00
-- url     : https://prove2.me/theorems/b9cb677a-9cb8-591e-8fde-b95f36b00a6b
-- title:
--   Dyadic support within the original LP retains half the objective
-- statement:
--   Let $I$ be a valid instance, let $b$ be a nonnegative integer horizon, and let $x$ be feasible in the time-indexed linear program. There is another solution $y$ feasible in that same program, supported on zero and the powers of two up to $b$, with
--   $$
--   \operatorname{obj}(y)\ge \tfrac12\operatorname{obj}(x).
--   $$
--
--   At a retained time $r$ both the objective and the constraints use the original coefficients. This permits a factor-two numerical approximation on the restricted time grid within the constant budget of Theorem 5.1.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora's Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#A2.SS1, Appendix B.1, compare Lemma B.1. Derived variant using the coefficients at the dyadic start itself in the original LP, rather than the shifted compact LP.

import Definitions.Def_PandoraKnapsack_Skipping_CompactLP

namespace PandoraKnapsack.Skipping

theorem dyadic_sparse_half {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) (b : ℕ)
    (x : LPArray n m) (hx : PsiFeasible I b x) :
    ∃ y : LPArray n m, PsiFeasible I b y ∧
      (∀ i j t, t ∉ breakpoints b → y i j t = 0) ∧
      psiObjective I b x / 2 ≤ psiObjective I b y := by sorry

end PandoraKnapsack.Skipping
