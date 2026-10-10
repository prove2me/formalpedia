-- Prove2me | Theorems.Thm_PriceQualityService_Dealer_optimal_level_sets
-- name    : PriceQualityService.Dealer.optimal_level_sets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:34:29.401235+00:00
-- url     : https://prove2.me/theorems/938b71d2-e046-4cf3-be95-a2df3924c8fc
-- title:
--   At the root $r^*$ of $r=H(r)$, long service on $\{x_i\ge r^*\}$ and short service on the rest of $\{z_i\ge r^*\}$ is optimal
-- statement:
--   Assume $t_s<t_l$, and $s_i>0$ and $a_i-b_iq_i\ge0$ for every product $i$. Let $r^*$ satisfy $r^*=H(r^*)$, and put
--
--   $$
--   S_l=\{i\in\mathcal N: x_i\ge r^*\},\qquad S_s=\{i\in\mathcal N: z_i\ge r^*\}\setminus S_l .
--   $$
--
--   Then $S_l$ and $S_s$ are disjoint, $\Pi^s(\mathbf p,\mathbf q;S_l,S_s)=r^*$, and $\Pi^s(\mathbf p,\mathbf q;S_l',S_s')\le\Pi^s(\mathbf p,\mathbf q;S_l,S_s)$ for every disjoint pair $(S_l',S_s')$.
--
--   This is the explicit optimal solution from which Theorem 5 is read off: the offered set $\{z_i\ge r^*\}$ is a markup-ordered assortment and the long-service set $\{x_i\ge r^*\}$ an adjusted markup-ordered set.
--
--   **Formalization Note** The three hypotheses are the model's standing assumptions made explicit. The root $r^*$ enters as any real with $r^*=H(r^*)$; such a root exists and is unique (the fixed-point milestone), so the statement is not vacuous.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 8 (PDF p. 41), Proof of Theorem 5 (last two paragraphs)

import Mathlib
import Definitions.Def_PriceQualityService_Dealer_Model
import Definitions.Def_PriceQualityService_Dealer_Breakpoints

open Finset

namespace PriceQualityService.Dealer

/-- Proof of Theorem 5, Online Supplement p. 8: assume `t_s < t_l`, `0 < s_i` and
`0 ≤ a_i − b_i q_i` for every product. If `r*` solves `r = H(r)`, then offering long service to
`S_l = {i | x_i ≥ r*}` and short service to `S_s = {i | z_i ≥ r*} \ S_l` is a feasible pair
whose profit is `r*` and which is optimal for problem (13). -/
theorem optimal_level_sets {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (hts : ts < tl)
    (hs : ∀ i, 0 < s i) (hg : ∀ i, 0 ≤ a i - b i * q i)
    (rstar : ℝ) (hrstar : rstar = bigH α a b c s p q ts tl rstar) :
    Disjoint (univ.filter fun i => rstar ≤ adjustedMarkup a b c s p q ts tl i)
        ((univ.filter fun i => rstar ≤ markup a b c p q ts i) \
          univ.filter fun i => rstar ≤ adjustedMarkup a b c s p q ts tl i) ∧
    dealerProfit α a b c s p q ts tl
        (univ.filter fun i => rstar ≤ adjustedMarkup a b c s p q ts tl i)
        ((univ.filter fun i => rstar ≤ markup a b c p q ts i) \
          univ.filter fun i => rstar ≤ adjustedMarkup a b c s p q ts tl i) = rstar ∧
    ∀ Sl Ss : Finset (Fin N), Disjoint Sl Ss →
      dealerProfit α a b c s p q ts tl Sl Ss ≤
        dealerProfit α a b c s p q ts tl
          (univ.filter fun i => rstar ≤ adjustedMarkup a b c s p q ts tl i)
          ((univ.filter fun i => rstar ≤ markup a b c p q ts i) \
            univ.filter fun i => rstar ≤ adjustedMarkup a b c s p q ts tl i) := by sorry

end PriceQualityService.Dealer
