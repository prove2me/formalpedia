-- Prove2me | Theorems.Thm_PriceQualityService_Dealer_eq_EC_11
-- name    : PriceQualityService.Dealer.eq_EC_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:33:02.352834+00:00
-- url     : https://prove2.me/theorems/c951cd7f-d5ba-43b8-bccf-e29d878cb7fb
-- title:
--   (EC.11): the dealer's profit is the unique root of $r=\sum_{S_l}h^l_i(r)+\sum_{S_s}h^s_i(r)$
-- statement:
--   Let $S_l,S_s\subseteq\mathcal N$ be disjoint, and let $h^l_i,h^s_i$ be as in the proof of Theorem 5. For every real $r$,
--
--   $$
--   r=\Pi^s(\mathbf p,\mathbf q;S_l,S_s)\iff r=\sum_{i\in S_l}h^l_i(r)+\sum_{i\in S_s}h^s_i(r).
--   $$
--
--   In particular the equation on the right has exactly one solution, and it is the dealer's profit from the pair $(S_l,S_s)$.
--
--   This substitution turns the ratio form of the MNL profit into a fixed-point equation that is additive over products; it is the first step of the proof of Theorem 5.
--
--   **Formalization Note** No sign condition on any parameter is needed; disjointness of $S_l$ and $S_s$ is the problem's feasibility condition (p. 22).
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 8 (PDF p. 41), Proof of Theorem 5, eq. (EC.11)

import Mathlib
import Definitions.Def_PriceQualityService_Dealer_Model
import Definitions.Def_PriceQualityService_Dealer_Breakpoints

open Finset

namespace PriceQualityService.Dealer

/-- (EC.11), Online Supplement p. 8: for a feasible (disjoint) pair `(S_l, S_s)`, a real `r`
equals the dealer's profit `Π^s(p, q; S_l, S_s)` if and only if
`r = ∑_{i ∈ S_l} h^l_i(r) + ∑_{i ∈ S_s} h^s_i(r)`; in particular that equation has exactly one
root, the profit. -/
theorem eq_EC_11 {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ)
    (Sl Ss : Finset (Fin N)) (hdisj : Disjoint Sl Ss) (r : ℝ) :
    r = dealerProfit α a b c s p q ts tl Sl Ss ↔
      r = ∑ i ∈ Sl, hLong α a b c s p q tl i r + ∑ i ∈ Ss, hShort α a b c s p q ts i r := by sorry

end PriceQualityService.Dealer
