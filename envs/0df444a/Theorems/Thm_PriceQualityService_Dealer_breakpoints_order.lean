-- Prove2me | Theorems.Thm_PriceQualityService_Dealer_breakpoints_order
-- name    : PriceQualityService.Dealer.breakpoints_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:31:59.986443+00:00
-- url     : https://prove2.me/theorems/0447b222-17d0-486c-ba6a-74747db644e2
-- title:
--   The breakpoints $x_i,y_i,z_i$ solve $h^l_i=h^s_i$, $h^l_i=0$, $h^s_i=0$, and $x_i\le y_i\le z_i$
-- statement:
--   Let $t_s<t_l$, and let product $i$ have $s_i>0$ and $a_i-b_iq_i\ge0$. Then
--
--   1. $x_i=(p_i-c_iq_i^2)-A_i(a_i-b_iq_i)$ is the unique solution of $h^l_i(x)=h^s_i(x)$;
--   2. $y_i=p_i-c_iq_i^2-t_l(a_i-b_iq_i)$ is the unique solution of $h^l_i(x)=0$;
--   3. $z_i=p_i-c_iq_i^2-t_s(a_i-b_iq_i)$ is the unique solution of $h^s_i(x)=0$;
--   4. the three breakpoints are ordered:
--   $$x_i\le y_i\le z_i .$$
--
--   The ordering of the breakpoints is what makes $h_i=\max\{h^l_i,h^s_i,0\}$ a three-piece function of $r$.
--
--   **Formalization Note** The hypotheses $t_s<t_l$, $s_i>0$ and $a_i-b_iq_i\ge0$ are standing assumptions of the model made explicit: $t_s,t_l$ are the shortest and longest durations (p. 7), $s_i$ is a service utility (p. 6) and $a_i-b_iq_i$ a service cost (p. 8). The first two make $A_i$ well defined; without the third the ordering $x_i\le y_i\le z_i$ fails.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), Online Supplement p. 8 (PDF p. 41), Proof of Theorem 5 (definition of x_i, y_i, z_i)

import Mathlib
import Definitions.Def_PriceQualityService_Dealer_Model
import Definitions.Def_PriceQualityService_Dealer_Breakpoints

open Finset

namespace PriceQualityService.Dealer

/-- Proof of Theorem 5, Online Supplement p. 8: for a product `i` with `t_s < t_l`, `0 < s_i` and
`0 ≤ a_i − b_i q_i`, the adjusted markup `x_i` is the unique solution of `h^l_i(x) = h^s_i(x)`,
the long-service markup `y_i = p_i − c_i q_i² − t_l(a_i − b_i q_i)` the unique solution of
`h^l_i(x) = 0`, the short-service markup `z_i = p_i − c_i q_i² − t_s(a_i − b_i q_i)` the unique
solution of `h^s_i(x) = 0`, and `x_i ≤ y_i ≤ z_i`. -/
theorem breakpoints_order {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (hts : ts < tl)
    (i : Fin N) (hs : 0 < s i) (hg : 0 ≤ a i - b i * q i) :
    (∀ r : ℝ, hLong α a b c s p q tl i r = hShort α a b c s p q ts i r ↔
      r = adjustedMarkup a b c s p q ts tl i) ∧
    (∀ r : ℝ, hLong α a b c s p q tl i r = 0 ↔ r = markup a b c p q tl i) ∧
    (∀ r : ℝ, hShort α a b c s p q ts i r = 0 ↔ r = markup a b c p q ts i) ∧
    adjustedMarkup a b c s p q ts tl i ≤ markup a b c p q tl i ∧
    markup a b c p q tl i ≤ markup a b c p q ts i := by sorry

end PriceQualityService.Dealer
