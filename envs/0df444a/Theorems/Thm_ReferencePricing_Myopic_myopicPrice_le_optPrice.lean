-- Prove2me | Theorems.Thm_ReferencePricing_Myopic_myopicPrice_le_optPrice
-- name    : ReferencePricing.Myopic.myopicPrice_le_optPrice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T09:47:15.671109+00:00
-- url     : https://prove2.me/theorems/33238de3-e01a-45c5-8d50-b46e7ad3ce05
-- title:
--   Proposition 1, first claim (§A.1, first paragraph) — the optimal price dominates the myopic price: p*(r) ≥ p̃(r)
-- statement:
--   Under the standing assumptions of §4 ($\bar p > 0$, $\alpha \in [0,1)$, $\beta \in (0,1)$, Assumptions 1–3, $R(0,r)=0$, $d$ differentiable), for every reference price $r \in P$,
--   $$\tilde p(r) = \operatorname*{arg\,max}_{p\in P} \Pi(p, r) \;\le\; \operatorname*{arg\,max}_{p\in P}\{\Pi(p,r) + \beta V(\alpha r + (1-\alpha) p)\} = p^*(r),$$
--   where both argmax are largest maximizers.
--
--   The myopic firm underprices at every state: taking into account the future value of a higher reference price can only raise the price. This is the first sentence of Proposition 1, stated separately as the base case of the path comparison.
--
--   **Formalization Note.** Both policies are largest maximizers (the paper's convention); with arbitrary maximizers the inequality can fail. Differentiability of $d$ is added as in the rest of §4.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 418, Proposition 1 (first sentence) and p. 425, §A.1, first paragraph

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_Assumptions
import Definitions.Def_ReferencePricing_Myopic_optPrice
import Definitions.Def_ReferencePricing_Myopic_myopicPrice

namespace ReferencePricing.Myopic

/-- Proposition 1, first sentence, as proved in §A.1, first paragraph (pp. 418, 425): for every
reference price `r ∈ P`, the myopic price is at most the optimal price, `p̃(r) ≤ p*(r)`
(both the largest maximizers of their objectives over `P = [0, p̄]`). -/
theorem myopicPrice_le_optPrice (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (α β pbar : ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hR0 : ∀ r, R 0 r = 0) (hd : Differentiable ℝ d)
    (hA1 : Assumption1 d R pbar) (hA2 : Assumption2 R) (hA3 : Assumption3 d R pbar) :
    ∀ r ∈ Set.Icc (0 : ℝ) pbar,
      myopicPrice (profit d R) pbar r ≤ optPrice (profit d R) α β pbar r := by sorry

end ReferencePricing.Myopic
