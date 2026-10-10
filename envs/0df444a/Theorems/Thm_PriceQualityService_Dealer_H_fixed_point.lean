-- Prove2me | Theorems.Thm_PriceQualityService_Dealer_H_fixed_point
-- name    : PriceQualityService.Dealer.H_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:32:54.787838+00:00
-- url     : https://prove2.me/theorems/b352da10-6775-48fa-9f59-453a66cb8c87
-- title:
--   $H(r)=\max_{S_l,S_s}\{\cdots\}=\sum_i h_i(r)$, and the root of $r=H(r)$ is the optimal profit
-- statement:
--   In the dealer's problem (13), the following hold.
--
--   1. For every real $r$,
--   $$H(r)=\max_{S_l,S_s}\Big\{\sum_{i\in S_l}h^l_i(r)+\sum_{i\in S_s}h^s_i(r)\Big\}=\sum_{i\in\mathcal N}h_i(r),$$
--   the maximum being taken over disjoint pairs $(S_l,S_s)$ of subsets of $\mathcal N$, and attained.
--   2. $H$ is non-increasing in $r$.
--   3. The equation $r=H(r)$ has exactly one real solution $r^*$.
--   4. $r^*$ is the optimal value of (13): $\Pi^s(\mathbf p,\mathbf q;S_l,S_s)\le r^*$ for every disjoint pair, with equality for some disjoint pair.
--
--   This reduces the combinatorial problem (13) to a scalar fixed-point equation.
--
--   **Formalization Note** The paper writes the maximum over $S_l,S_s\subseteq\mathcal N$; disjointness is the feasibility condition of (13) (p. 22) and is part of the index set here. Maximality is stated with `IsGreatest`, so attainment is part of the claim. No sign condition on any parameter is needed for these four facts.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 8 (PDF p. 41), Proof of Theorem 5 (display defining H(r))

import Mathlib
import Definitions.Def_PriceQualityService_Dealer_Model
import Definitions.Def_PriceQualityService_Dealer_Breakpoints

open Finset

namespace PriceQualityService.Dealer

/-- Proof of Theorem 5, Online Supplement p. 8: for every `r`,
`H(r) = max_{S_l, S_s} {∑_{i ∈ S_l} h^l_i(r) + ∑_{i ∈ S_s} h^s_i(r)} = ∑_i h_i(r)`, the maximum
taken over disjoint pairs; `H` is decreasing; the equation `r = H(r)` has a unique root `r*`; and
`r*` is the optimal value of problem (13), attained by some disjoint pair. -/
theorem H_fixed_point {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) :
    (∀ r : ℝ, IsGreatest
        {v : ℝ | ∃ Sl Ss : Finset (Fin N), Disjoint Sl Ss ∧
          v = ∑ i ∈ Sl, hLong α a b c s p q tl i r + ∑ i ∈ Ss, hShort α a b c s p q ts i r}
        (bigH α a b c s p q ts tl r)) ∧
    Antitone (bigH α a b c s p q ts tl) ∧
    (∃! r : ℝ, r = bigH α a b c s p q ts tl r) ∧
    (∀ r : ℝ, r = bigH α a b c s p q ts tl r →
      IsGreatest
        {v : ℝ | ∃ Sl Ss : Finset (Fin N), Disjoint Sl Ss ∧
          v = dealerProfit α a b c s p q ts tl Sl Ss} r) := by sorry

end PriceQualityService.Dealer
