-- Prove2me | Theorems.Thm_ReferencePricing_Myopic_myopicPricePath_monotone
-- name    : ReferencePricing.Myopic.myopicPricePath_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T09:37:31.768658+00:00
-- url     : https://prove2.me/theorems/50444edc-39ba-491c-922a-20f675e41931
-- title:
--   §A.1, third paragraph — the myopic price path is increasing if p̃(r₀) ≥ r₀ and decreasing if p̃(r₀) ≤ r₀
-- statement:
--   Under the standing assumptions of §4 ($\bar p > 0$, $\alpha \in [0,1)$, Assumptions 1–3, $R(0,r)=0$, $d$ differentiable), let $r_0 \in P$ and let $p^M_t = \tilde p(r^M_t)$ be the myopic price path from $r_0$. Then
--   $$\tilde p(r_0) \ge r_0 \implies p^M_0 \le p^M_1 \le p^M_2 \le \cdots, \qquad \tilde p(r_0) \le r_0 \implies p^M_0 \ge p^M_1 \ge p^M_2 \ge \cdots.$$
--
--   The whole myopic price path, from time $0$ on, moves in one direction, determined by whether the first myopic price is above or below the initial reference price. This gives the "monotonically" in Proposition 1's convergence claim.
--
--   **Formalization Note.** The paper proves the increasing case and states "the other case is symmetric"; both cases are included. Monotonicity is of the whole sequence, not of a tail. The discount factor $\beta$ does not enter the myopic path and is not a parameter.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 425, §A.1, third paragraph, first three sentences

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_Assumptions
import Definitions.Def_ReferencePricing_Myopic_myopicPrice

namespace ReferencePricing.Myopic

/-- §A.1, third paragraph, first three sentences (p. 425): if `p̃(r₀) ≥ r₀` the myopic price path
`p^M_t` is increasing in `t`, and in the symmetric case `p̃(r₀) ≤ r₀` it is decreasing in `t`. -/
theorem myopicPricePath_monotone (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (α pbar : ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1)
    (hR0 : ∀ r, R 0 r = 0) (hd : Differentiable ℝ d)
    (hA1 : Assumption1 d R pbar) (hA2 : Assumption2 R) (hA3 : Assumption3 d R pbar) :
    ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar,
      (r₀ ≤ myopicPrice (profit d R) pbar r₀ → Monotone (myopicPricePath (profit d R) α pbar r₀)) ∧
        (myopicPrice (profit d R) pbar r₀ ≤ r₀ →
          Antitone (myopicPricePath (profit d R) α pbar r₀)) := by sorry

end ReferencePricing.Myopic
