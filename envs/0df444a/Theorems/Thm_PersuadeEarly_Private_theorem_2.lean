-- Prove2me | Theorems.Thm_PersuadeEarly_Private_theorem_2
-- name    : PersuadeEarly.Private.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:23.963895+00:00
-- url     : https://prove2.me/theorems/983ffa05-f9c9-487b-8dd1-0bdd24ee7ee6
-- title:
--   Theorem 2, p. 17 — if $q_L\le\bar F(p^m)$, the personalized mechanism (PS1)–(PS2) is optimal and $R_{private}>R^*_\phi$
-- statement:
--   Under the standing assumptions, suppose $q_L\le\bar F(p^m)$, and let $p_1=\bar F^{-1}(q_L)$. Then:
--   1. the price condition (14), $\bar F(p_2)-p_2f(p_2)=\bar F(\bar v)$, has a solution $p_2\in(0,p_1)$;
--   2. for every solution $p_2\in[0,p_1)$ of (14), the private mechanism (PS2) at prices $p_1,p_2$ is valid and obedient;
--   3. its revenue is at least that of every valid obedient signaling mechanism, at any prices $p_1',p_2'\ge0$ (including $p_2'>p_1'$) and with any finite latent signal space;
--   4. its revenue is strictly larger than the optimal public-signaling revenue:
--   $$R^*_\phi<R_{private}.$$
--
--   Personalized information has value: by privately telling some high-valuation customers to buy now, the firm creates an availability risk that public signals cannot, and strictly beats every public signaling mechanism.
--
--   **Formalization Note** The paper's game (Definitions 1–2) is represented by obedient straightforward mechanisms with aggregate masses and a finite latent index, the class its proofs reduce to (p. 39, footnote 5). "The optimal" is stated as "an optimal": optimal mechanisms need not be unique. $R_{private}$ is the revenue of the mechanism (PS2) itself; the milestone (16) identifies it with the formula. The existence part keeps the statement from being vacuous; the root lies in $(0,p_1)$, not in $(0,p^m)$ as p. 45 says (that fails when $\bar F(\bar v)=0$ at $p_2=p^m$).
-- source:
--   Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 17, Theorem 2

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation
import Definitions.Def_PersuadeEarly_Private_Mechanism
import Definitions.Def_PersuadeEarly_Private_PrivateMech

namespace PersuadeEarly.Private

/-- Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 17, Theorem 2: if `qL ≤ F̄(p^m)`, then the private signaling mechanism described by (PS1)
and (PS2) is the optimal signaling mechanism. In this case, `R_private > R*_ϕ`.

Stated as: if `qL ≤ F̄(p^m)`, then (i) the price condition (14) has a root `p2 ∈ (0, p1)`, where
`p1 = F̄^{-1}(qL)`; and (ii) for every root `p2 ∈ [0, p1)` of (14), the mechanism (PS2) is valid and
obedient, earns at least the revenue of every valid obedient mechanism at any prices
`p1', p2' ≥ 0` and any finite latent index, and earns strictly more than `R*_ϕ`.

**Formalization Note** The game of Definitions 1–2 is replaced by obedient straightforward
mechanisms with aggregate masses and a finite latent index (`Mech`), the class the paper's proofs
reduce to (p. 39, footnote 5). "The optimal" is stated as "an optimal" (ties exist). Prices
`p2' > p1'` are included (p. 8). (14) is written `F̄(p2) − p2 f(p2) = F̄(v̄)`. The existence conjunct
keeps the second part from being vacuous; the root lies in `(0, p1)` (p. 45 says `(0, p^m)`, which
fails when `F̄(v̄) = 0` at `p2 = p^m`). -/
theorem theorem_2 (M : Model) (hM : M.Standing) (hq : M.qL ≤ M.Fbar M.pm) :
    (∃ p2, 0 < p2 ∧ p2 < M.FbarInv M.qL ∧ PS14 M p2) ∧
    ∀ p2, 0 ≤ p2 → p2 < M.FbarInv M.qL → PS14 M p2 →
      (psMech M p2).Valid ∧ (psMech M p2).Obedient ∧
      (∀ (n : ℕ) (N : Mech M n), N.Valid → N.Obedient → N.revenue ≤ (psMech M p2).revenue) ∧
      Rphi M < (psMech M p2).revenue := by sorry

end PersuadeEarly.Private
