-- Prove2me | Theorems.Thm_PersuadeEarly_Private_theorem_2_optimal
-- name    : PersuadeEarly.Private.theorem_2_optimal
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-22T05:28:23.979036+00:00
-- url     : https://prove2.me/theorems/234b8944-ffeb-441b-924b-75f6135a983c
-- title:
--   Theorem 2 (optimality), p. 17 — if $q_L\le\bar F(p^m)$, the mechanism (PS1)–(PS2) earns at least every valid obedient mechanism
-- statement:
--   Under the standing assumptions, suppose $q_L\le\bar F(p^m)$, and let $p_1=\bar F^{-1}(q_L)$. Let $p_2\in[0,p_1)$ be a solution of the price condition (14),
--   $$\bar F(p_2)-p_2f(p_2)=\bar F(\bar v),$$
--   where $\bar v$ is defined in (15). Then the personalized Buy/Wait/No mechanism (PS2) at prices $(p_1,p_2)$ is optimal: for every finite latent index set $\{0,\dots,n-1\}$ and every valid, obedient straightforward signaling mechanism $N$ (at any prices $p_1',p_2'\ge0$, including $p_2'>p_1'$),
--   $$R(N)\;\le\;R(\text{PS2 at }p_1,p_2).$$
--
--   This is the optimality half of Theorem 2 of the paper ("the private signaling mechanism described by (PS1) and (PS2) is the optimal signaling mechanism"). Together with the existence of a root of (14), the validity and obedience of (PS2) (milestone (16)), and the comparison with the public optimum $R^*_\phi$, it yields the full Theorem 2.
--
--   **Formalization Note** Mechanisms are the aggregate straightforward mechanisms `Mech M n` with a finite latent index, as in the mission's goal statement (`PersuadeEarly.Private.theorem_2`); this is exactly the third conjunct of that statement, isolated as a lemma.
-- source:
--   Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 17, Theorem 2 (optimality of the private mechanism (PS1)-(PS2))

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation
import Definitions.Def_PersuadeEarly_Private_Mechanism
import Definitions.Def_PersuadeEarly_Private_PrivateMech

namespace PersuadeEarly.Private

/-- Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized
Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 17, Theorem 2, optimality
part: if `qL ≤ F̄(p^m)`, the private signaling mechanism (PS1)–(PS2) is the optimal signaling
mechanism. Stated as: for every root `p2 ∈ [0, p1)` of (14), `p1 = F̄^{-1}(qL)`, the revenue of
(PS2) is at least that of every valid obedient mechanism at any prices and with any finite latent
index. -/
theorem theorem_2_optimal (M : Model) (hM : M.Standing) (hq : M.qL ≤ M.Fbar M.pm) :
    ∀ p2, 0 ≤ p2 → p2 < M.FbarInv M.qL → PS14 M p2 →
      ∀ (n : ℕ) (N : Mech M n), N.Valid → N.Obedient → N.revenue ≤ (psMech M p2).revenue := by sorry

end PersuadeEarly.Private
