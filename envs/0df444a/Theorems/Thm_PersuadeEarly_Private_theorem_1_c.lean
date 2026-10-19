-- Prove2me | Theorems.Thm_PersuadeEarly_Private_theorem_1_c
-- name    : PersuadeEarly.Private.theorem_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:31.04564+00:00
-- url     : https://prove2.me/theorems/657c764e-c989-418d-9aac-09e2e7522926
-- title:
--   Theorem 1 (c), p. 15 — the optimal public-signaling revenue is $R^*_\phi$ (11)
-- statement:
--   Under the standing assumptions (any $q_L\in(0,1]$), the largest revenue a valid public signaling mechanism can earn, over all prices $p_1,p_2\ge0$ and all finite public signal spaces, is
--   $$R^*_\phi=P(L)\,p_1\bar F(p_1)+P(H)\,p_2\bar F(p_2),\qquad p_1=\max\{\bar F^{-1}(q_L),p^m\},\ p_2=p^m, \tag{11}$$
--   and this value is attained by some valid public mechanism.
--
--   Public information cannot create availability risk that customers fail to unravel: the best public mechanism earns what prices alone earn. The proof of Theorem 2 uses this value to dispose of the case in which the period-2 market fits in the low inventory.
--
--   **Formalization Note** Public mechanisms are the straightforward mechanisms whose recommendations depend only on the public signal and the valuation, and which are obedient given each realized signal. Parts (a)–(b) of Theorem 1 (which mechanisms attain $R^*_\phi$) are not stated.
-- source:
--   Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 15, Theorem 1 (c), (11)

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation
import Definitions.Def_PersuadeEarly_Private_Mechanism

namespace PersuadeEarly.Private

/-- Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 15, Theorem 1 (c): the firm's revenue under any optimal public signaling mechanism is
`R*_ϕ = P(L) p1 F̄(p1) + P(H) p2 F̄(p2)` (11), with `p1 = max{F̄^{-1}(qL), p^m}` and `p2 = p^m`.

Stated as: `R*_ϕ` is the greatest revenue of a valid public signaling mechanism (with any finite
public signal space `Fin n` and any prices `p1, p2 ≥ 0`); in particular it is attained.

**Formalization Note** Public mechanisms are the aggregate straightforward mechanisms whose
recommendations depend only on the public signal `k` and the valuation, and which are obedient
given each realized `k` (`Mech.IsPublic`). Holds for every `qL ∈ (0, 1]`. -/
theorem theorem_1_c (M : Model) (hM : M.Standing) :
    IsGreatest {r | ∃ (n : ℕ) (N : Mech M n), N.Valid ∧ N.IsPublic ∧ N.revenue = r} (Rphi M) := by sorry

end PersuadeEarly.Private
