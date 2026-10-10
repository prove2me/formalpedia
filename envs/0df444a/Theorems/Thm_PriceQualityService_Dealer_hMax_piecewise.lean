-- Prove2me | Theorems.Thm_PriceQualityService_Dealer_hMax_piecewise
-- name    : PriceQualityService.Dealer.hMax_piecewise
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:32:02.322989+00:00
-- url     : https://prove2.me/theorems/0529e83e-50b7-47de-a1d4-d7fcd99a8344
-- title:
--   $h_i=h^l_i$ on $r\le x_i$, $h_i=h^s_i$ on $x_i<r\le z_i$, $h_i=0$ on $r>z_i$
-- statement:
--   Let $t_s<t_l$, and let product $i$ have $s_i>0$ and $a_i-b_iq_i\ge0$. Then $h_i(r)=\max\{h^l_i(r),h^s_i(r),0\}$ satisfies
--
--   $$
--   h_i(r)=\begin{cases}h^l_i(r), & r\le x_i,\\ h^s_i(r), & x_i<r\le z_i,\\ 0, & r>z_i.\end{cases}
--   $$
--
--   Evaluated at the optimal value $r^*$, this says which service, if any, each product should receive.
--
--   **Formalization Note** The three hypotheses are the model's standing assumptions made explicit, as in the breakpoint-order milestone.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 8 (PDF p. 41), Proof of Theorem 5 (characterization of h_i)

import Mathlib
import Definitions.Def_PriceQualityService_Dealer_Model
import Definitions.Def_PriceQualityService_Dealer_Breakpoints

open Finset

namespace PriceQualityService.Dealer

/-- Proof of Theorem 5, Online Supplement p. 8: for a product `i` with `t_s < t_l`, `0 < s_i` and
`0 ≤ a_i − b_i q_i`, `h_i(r) = h^l_i(r)` for `r ≤ x_i`, `h_i(r) = h^s_i(r)` for `x_i < r ≤ z_i`,
and `h_i(r) = 0` for `r > z_i`. -/
theorem hMax_piecewise {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (hts : ts < tl)
    (i : Fin N) (hs : 0 < s i) (hg : 0 ≤ a i - b i * q i) :
    (∀ r : ℝ, r ≤ adjustedMarkup a b c s p q ts tl i →
      hMax α a b c s p q ts tl i r = hLong α a b c s p q tl i r) ∧
    (∀ r : ℝ, adjustedMarkup a b c s p q ts tl i < r → r ≤ markup a b c p q ts i →
      hMax α a b c s p q ts tl i r = hShort α a b c s p q ts i r) ∧
    (∀ r : ℝ, markup a b c p q ts i < r → hMax α a b c s p q ts tl i r = 0) := by sorry

end PriceQualityService.Dealer
