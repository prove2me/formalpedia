-- Prove2me | Theorems.Thm_ReferencePricing_Myopic_myopic_steady_state_unique
-- name    : ReferencePricing.Myopic.myopic_steady_state_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T09:37:25.349874+00:00
-- url     : https://prove2.me/theorems/75f32969-8ffb-467e-b75e-1a0ba7ab1fc4
-- title:
--   §A.1, third paragraph — the myopic steady-state price p^{M*} is unique
-- statement:
--   Under the standing assumptions of §4 ($\bar p > 0$, Assumptions 1–3, $R(0,r)=0$, $d$ differentiable), there is at most one **myopic steady state**, i.e. one price $p \in P$ with $\tilde p(p) = p$:
--   $$p, q \in P,\ \tilde p(p) = p,\ \tilde p(q) = q \implies p = q.$$
--
--   The paper argues that an (interior) myopic steady state solves the first-order condition $\Pi_p(p, p) = \pi'(p) - p\lambda(p) = 0$, whose left side is strictly decreasing by Assumption 3(b). This uniqueness is what makes the limit in Proposition 1 one price for all initial reference prices.
--
--   **Formalization Note.** The Lean statement is uniqueness of fixed points of $\tilde p$ on all of $P$, including the endpoints $0$ and $\bar p$, where the first-order condition is only an inequality; the first-order route is not part of the statement.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 425, §A.1, third paragraph, last two sentences

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_Assumptions
import Definitions.Def_ReferencePricing_Myopic_myopicPrice

namespace ReferencePricing.Myopic

/-- §A.1, third paragraph, last two sentences (p. 425): the myopic steady-state price is unique —
there is at most one `p ∈ P` with `p̃(p) = p`. -/
theorem myopic_steady_state_unique (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (pbar : ℝ)
    (hpbar : 0 < pbar) (hR0 : ∀ r, R 0 r = 0) (hd : Differentiable ℝ d)
    (hA1 : Assumption1 d R pbar) (hA2 : Assumption2 R) (hA3 : Assumption3 d R pbar) :
    ∀ p ∈ Set.Icc (0 : ℝ) pbar, ∀ q ∈ Set.Icc (0 : ℝ) pbar,
      myopicPrice (profit d R) pbar p = p → myopicPrice (profit d R) pbar q = q → p = q := by sorry

end ReferencePricing.Myopic
