-- Prove2me | Theorems.Thm_TurnTables_Reciprocal_optimal_strike
-- name    : TurnTables.Reciprocal.optimal_strike
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:18.837372+00:00
-- url     : https://prove2.me/theorems/d02a8e06-5380-46e8-a405-c26d0b48b673
-- title:
--   Proposition 5, p. 22 — prior-optimal strike price
-- statement:
--   Suppose both parties have acquired the other's capability, with $0<\gamma<1$, $0<V_1$, and $2V_1<V_2$. For either implementation type $\Gamma_R\in\{\gamma,1\}$ of the offeror, let $U_R(B)$ be its expected buyout payoff at price $B$ when the offeree's private type is equally likely to be partial or full and responds optimally, accepting an indifferent offer. Then
--
--   $$
--   U_R(B)\le U_R\!\left(\frac{\gamma V_2}{2}\right)
--   \qquad\text{for every }B\ge0.
--   $$
--
--   This isolates the price clause of Proposition 5; it asserts weak optimality, not uniqueness.
--
--   **Formalization Note** Price is evaluated against the prior distribution of the offeree's type, as indicated by the paper's separation of the price and offer decisions. The source model supplies $V_1>0$, although this price comparison does not use it.
-- source:
--   Taneri & Crama, Turning the Tables in R&D Licensing Contracts, SSRN 3711872 (version of October 15, 2020), p. 22, §4.4 and Proposition 5 strike-price clause

import Mathlib
import Definitions.Def_TurnTables_Reciprocal_Model

namespace TurnTables.Reciprocal

theorem optimal_strike (P : Params) (hP : P.Standing) :
    ∀ R : Impl, ∀ B : ℝ, 0 ≤ B →
      offerorPriorPay P R B ≤ offerorPriorPay P R (strikeB P) := by sorry

end TurnTables.Reciprocal
