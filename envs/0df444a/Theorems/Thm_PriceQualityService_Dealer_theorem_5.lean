-- Prove2me | Theorems.Thm_PriceQualityService_Dealer_theorem_5
-- name    : PriceQualityService.Dealer.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:33:15.159883+00:00
-- url     : https://prove2.me/theorems/b96d27fa-4307-4bde-8752-ef1b390764ee
-- title:
--   Theorem 5: a markup-ordered assortment is optimal, with long service on an adjusted markup-ordered subset
-- statement:
--   Consider the dealer's problem (13): prices $p_i$ and qualities $q_i$ are fixed, and the dealer chooses disjoint sets $S_l,S_s\subseteq\mathcal N$ of products offered with long service $t_l$ and short service $t_s$ to maximize $\Pi^s(\mathbf p,\mathbf q;S_l,S_s)$. Write $z_i=p_i-c_iq_i^2-t_s(a_i-b_iq_i)$ for the markup with short service, and $x_i=(p_i-c_iq_i^2)-A_i(a_i-b_iq_i)$ with $A_i=\frac{t_l e^{t_ls_i}-t_s e^{t_ss_i}}{e^{t_ls_i}-e^{t_ss_i}}$ for the adjusted markup. A **markup-ordered assortment** is a set of the form $\{i: z_i\ge\theta\}$ and an **adjusted markup-ordered set** one of the form $\{i: x_i\ge\theta'\}$.
--
--   **Theorem 5.** Assume $t_s<t_l$, and $s_i>0$ and $a_i-b_iq_i\ge0$ for every product. Then there are thresholds $\theta,\theta'$ such that, with $S_{i^*}=\{i: z_i\ge\theta\}$ and $S_{j^\natural}=\{i: x_i\ge\theta'\}$:
--
--   1. (a) $S_{i^*}$ is an optimal offer set for (13);
--   2. (b) $S_{j^\natural}\subseteq S_{i^*}$, and attaching the long service to $S_{j^\natural}$ and the short service to $S_{i^*}\setminus S_{j^\natural}$ is optimal:
--   $$
--   \Pi^s(\mathbf p,\mathbf q;S_l,S_s)\le\Pi^s\big(\mathbf p,\mathbf q;S_{j^\natural},S_{i^*}\setminus S_{j^\natural}\big)\quad\text{for all disjoint }S_l,S_s\subseteq\mathcal N .
--   $$
--
--   Consequently at most $O(N^2)$ candidate pairs need to be examined, and long service goes to the products with the highest adjusted profit margins.
--
--   **Formalization Note** The paper relabels products by decreasing markup and calls a prefix $\{1,\dots,i\}$ a markup-ordered assortment. Here such sets are the upper level sets $\{i: z_i\ge\theta\}$ and $\{i: x_i\ge\theta'\}$; every level set is a prefix of every decreasing relabelling, so the statement holds whatever tie-break the relabelling uses. The empty set and the full set are allowed. Parts (a) and (b) share the same $S_{i^*}$: (a) is the optimality of the pair in (b), whose union is $S_{i^*}$. The hypotheses $t_s<t_l$, $s_i>0$ and $a_i-b_iq_i\ge0$ are the model's standing assumptions made explicit (shortest and longest duration, service utility, service cost); the first two make $A_i$ well defined, and without the third part (b) is false.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 23, Theorem 5 (orderings pp. 22–23; proof Online Supplement p. 8, PDF p. 41)

import Mathlib
import Definitions.Def_PriceQualityService_Dealer_Model
import Definitions.Def_PriceQualityService_Dealer_Breakpoints

open Finset

namespace PriceQualityService.Dealer

/-- Theorem 5, p. 23. Assume `t_s < t_l`, `0 < s_i` and `0 ≤ a_i − b_i q_i` for every product.
(a) Some markup-ordered assortment `S = {i | z_i ≥ θ}`, `z_i = p_i − c_i q_i² − t_s(a_i − b_i q_i)`,
is an optimal offer set for problem (13); (b) some adjusted markup-ordered set
`L = {i | x_i ≥ θ'}` lies within `S`, and attaching the long service to `L` and the short service
to `S \ L` is optimal among all disjoint pairs `(S_l, S_s)`. -/
theorem theorem_5 {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (hts : ts < tl)
    (hs : ∀ i, 0 < s i) (hg : ∀ i, 0 ≤ a i - b i * q i) :
    ∃ θ θ' : ℝ,
      (univ.filter fun i => θ' ≤ adjustedMarkup a b c s p q ts tl i) ⊆
          (univ.filter fun i => θ ≤ markup a b c p q ts i) ∧
      ∀ Sl Ss : Finset (Fin N), Disjoint Sl Ss →
        dealerProfit α a b c s p q ts tl Sl Ss ≤
          dealerProfit α a b c s p q ts tl
            (univ.filter fun i => θ' ≤ adjustedMarkup a b c s p q ts tl i)
            ((univ.filter fun i => θ ≤ markup a b c p q ts i) \
              univ.filter fun i => θ' ≤ adjustedMarkup a b c s p q ts tl i) := by sorry

end PriceQualityService.Dealer
