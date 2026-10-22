-- Prove2me | Theorems.Thm_PersuadeEarly_Private_eq_16
-- name    : PersuadeEarly.Private.eq_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:36.277997+00:00
-- url     : https://prove2.me/theorems/fc20bc81-3b38-437b-a4ca-b97f52dd4c8e
-- title:
--   §5.2, (16), p. 17 — the mechanism (PS2) is obedient and earns $R_{private}$
-- statement:
--   Under the standing assumptions, let $p_1=\bar F^{-1}(q_L)$ and let $0\le p_2<p_1$ satisfy the price condition (14) of (PS1), $\bar F(p_2)-p_2f(p_2)=\bar F(\bar v)$. Then the private signaling mechanism (PS2) at prices $p_1,p_2$ is a valid mechanism, every customer finds it incentive compatible to follow its recommendation (it satisfies (Buy-1)–(No)), and its revenue is
--   $$R_{private}=P(H)p_2\bar F(p_2)+P(H)(p_1-p_2)\bar F(\bar v)+P(L)\int_{p_1}^{\bar v}(v-p_1)\,dF(v)+P(L)p_1q_L. \tag{16}$$
--
--   This ties the formula (16) to the mechanism: it is the revenue the personalized mechanism actually earns.
--
--   **Formalization Note** The scope is the printed one, the prices of (PS1); $p_2<p_1$ is presupposed by (PS2)(b)(ii) and by the division in (13).
-- source:
--   Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 17, §5.2, (16)

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation
import Definitions.Def_PersuadeEarly_Private_Mechanism
import Definitions.Def_PersuadeEarly_Private_PrivateMech

namespace PersuadeEarly.Private

/-- Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 17, §5.2, (16): "customers find it incentive compatible to follow the firm's
recommendation in this private mechanism. The revenue achieved by this private mechanism is equal
to R_private" (16).

Stated as: for every `p2 ∈ [0, p1)` satisfying the price condition (14) of (PS1),
`p1 = F̄^{-1}(qL)`, the mechanism (PS2) is valid and obedient and its revenue is `R_private`.

**Formalization Note** The scope is the printed one: the prices of (PS1), i.e. `p1 = F̄^{-1}(qL)`
and `p2` a root of (14) (written `F̄(p2) − p2 f(p2) = F̄(v̄)`), with `p2 < p1` as (PS2)(b)(ii) and
(13) presuppose. -/
theorem eq_16 (M : Model) (hM : M.Standing) :
    ∀ p2 : ℝ, 0 ≤ p2 → p2 < M.FbarInv M.qL → PS14 M p2 →
      (psMech M p2).Valid ∧ (psMech M p2).Obedient ∧ (psMech M p2).revenue = Rprivate M p2 := by sorry

end PersuadeEarly.Private
