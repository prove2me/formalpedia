-- Prove2me | Theorems.Thm_WagelmansELS_Efficient_proposition_2
-- name    : WagelmansELS.Efficient.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:59:07.778226+00:00
-- url     : https://prove2.me/theorems/5f25c973-fb16-4203-b4f6-b39ea09f090d
-- title:
--   Proposition 2: consecutive candidate costs compare by their ratio
-- statement:
--   Fix $1\le i\le n$. Let $k\in E_i$ be nonsentinel and let $l=\operatorname{succ}_i(k)$, so $k<l$ are consecutive efficient periods. Write $r_i(k)=[G(k)-G(l)]/[D(k)-D(l)]$. Then
--   $$r_i(k)<c_i\quad\Longrightarrow\quad c_i[D(i)-D(k)]+G(k)<c_i[D(i)-D(l)]+G(l),$$
--   and otherwise
--   $$c_i[D(i)-D(k)]+G(k)\ge c_i[D(i)-D(l)]+G(l).$$
--
--   The comparison explains why crossing the marginal-cost threshold changes the preferred efficient period. It is the numbered fact used by the paper's display after Proposition 2.
--
--   **Formalization Note** The successor is evaluated only at a nonsentinel efficient period, where the denominator is positive. Equality belongs to the “otherwise” case.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), p. S149, Proposition 2

import Mathlib
import Definitions.Def_WagelmansELS_Efficient_ThresholdRule

namespace WagelmansELS.Efficient

/-- Proposition 2, p. S149: the ratio decides which of two consecutive efficient
periods has the lower candidate cost. -/
theorem proposition_2 (P : Instance) (i k : ℕ)
    (hi : 1 ≤ i) (hin : i ≤ P.n)
    (hk : k ∈ P.E i) (hnext : k < P.n + 1) :
    (P.ratio i k < P.c i → P.score i k < P.score i (P.succ i k)) ∧
    (¬ P.ratio i k < P.c i → P.score i (P.succ i k) ≤ P.score i k) := by sorry

end WagelmansELS.Efficient
