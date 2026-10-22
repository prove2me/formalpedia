-- Prove2me | Theorems.Thm_ReferencePricing_Myopic_myopic_underprices_along_paths
-- name    : ReferencePricing.Myopic.myopic_underprices_along_paths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T09:47:43.032164+00:00
-- url     : https://prove2.me/theorems/b6d6e097-d701-4fe2-bc08-52b9dce2b6d4
-- title:
--   §A.1, second paragraph — along the two firms' paths from the same r₀, r^M_t ≤ r*_t and p^M_t ≤ p*_t for all t
-- statement:
--   Under the standing assumptions of §4, let a myopic firm and an optimizing firm start from the same initial reference price $r_0 \in P$, with state paths $r^M_t$, $r^*_t$ and price paths $p^M_t = \tilde p(r^M_t)$, $p^*_t = p^*(r^*_t)$. Then for every $t \ge 0$
--   $$r^M_t \le r^*_t \qquad\text{and}\qquad p^M_t \le p^*_t .$$
--
--   Each firm follows its own trajectory of consumer expectations; the claim is that the myopic firm's prices and the reference prices it induces stay below the optimal firm's at every time. The paper proves it by induction on $t$ from $\tilde p \le p^*$, monotonicity of $\tilde p$ (Lemma 1) and memory equation (1).
--
--   **Formalization Note.** Proposition 1's second sentence asserts only $p^M_t \le p^*_t$; the state inequality $r^M_t \le r^*_t$ is the induction hypothesis of the paper's proof and is included as part of this milestone's statement. Differentiability of $d$ is added as in the rest of §4.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 425, §A.1, second paragraph

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_Assumptions
import Definitions.Def_ReferencePricing_Myopic_optPrice
import Definitions.Def_ReferencePricing_Myopic_myopicPrice

namespace ReferencePricing.Myopic

/-- §A.1, second paragraph (p. 425): starting both firms from the same initial reference price
`r₀ ∈ P`, at every time `t` the myopic firm's reference price and price are at most the optimizing
firm's: `r^M_t ≤ r*_t` and `p^M_t ≤ p*_t`. -/
theorem myopic_underprices_along_paths (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (α β pbar : ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hR0 : ∀ r, R 0 r = 0) (hd : Differentiable ℝ d)
    (hA1 : Assumption1 d R pbar) (hA2 : Assumption2 R) (hA3 : Assumption3 d R pbar) :
    ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar, ∀ t : ℕ,
      myopicState (profit d R) α pbar r₀ t ≤ statePath (profit d R) α β pbar r₀ t ∧
        myopicPricePath (profit d R) α pbar r₀ t ≤ pricePath (profit d R) α β pbar r₀ t := by sorry

end ReferencePricing.Myopic
