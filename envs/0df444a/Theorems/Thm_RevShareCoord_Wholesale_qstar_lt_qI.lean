-- Prove2me | Theorems.Thm_RevShareCoord_Wholesale_qstar_lt_qI
-- name    : RevShareCoord.Wholesale.qstar_lt_qI
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:06:36.200303+00:00
-- url     : https://prove2.me/theorems/d25aa6d6-04ba-48a1-9812-97e0b2a07ed8
-- title:
--   Sec. 4.1.1, p. 16 — the supplier induces less than the integrated quantity: 0 < q* < q_I
-- statement:
--   Consider the single-retailer model of Sec. 1 with the assumptions of Sec. 4.1.1: $R$ strictly concave on $[0,\infty)$ with $R(0)=0$, derivative $R'$ on $[0,\infty)$, second derivative $R''$ on $(0,\infty)$, unit cost $c>0$, $R'(0) > c$, $R'(Q) < c$ for some $Q$, and $R'(q)+qR''(q)$ decreasing. Let
--
--   - $q^* \ge 0$ maximize the supplier's profit $\pi_s(q) = q(R'(q)-c)$ over $q \ge 0$ (the supplier's optimal quantity to induce with a wholesale-price contract), and
--   - $q_I \ge 0$ maximize the supply chain profit $\Pi(q) = R(q) - qc$ over $q \ge 0$ (the integrated channel's quantity).
--
--   Then
--
--   $$
--   0 < q^* < q_I .
--   $$
--
--   So the wholesale-price contract that is best for the supplier leaves total supply chain profit below its optimum: double marginalization.
--
--   **Formalization Note** The paper justifies the inequality by "$qR''(q) < 0$". No sign hypothesis on $R''$ is added: in the model the conclusion holds as stated, so it is stated without one. $q^*$ and $q_I$ are characterized as maximizers, not as roots of the first-order conditions.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 16 (PDF 17), Section 4.1.1, sentence after Eq. (10) comparing (10) with (1)

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

namespace RevShareCoord.Wholesale

/-- Sec. 4.1.1 (p. 16): the supplier's optimal quantity to induce `q*` (a maximizer of `π_s`
on `[0, ∞)`) is positive and strictly below the integrated-channel quantity `q_I` (a maximizer
of `Π` on `[0, ∞)`). -/
theorem qstar_lt_qI (M : Model) (qs qI : ℝ) (hqs0 : 0 ≤ qs)
    (hqs : IsMaxOn (supplierProfit M.R' M.c) (Set.Ici 0) qs)
    (hqI0 : 0 ≤ qI) (hqI : IsMaxOn (chainProfit M.R M.c) (Set.Ici 0) qI) :
    0 < qs ∧ qs < qI := by sorry

end RevShareCoord.Wholesale
