-- Prove2me | Theorems.Thm_TurnTables_Reciprocal_proposition_5
-- name    : TurnTables.Reciprocal.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:22.193791+00:00
-- url     : https://prove2.me/theorems/dd84eef6-2ea5-4edc-87c1-1b86020b4567
-- title:
--   Proposition 5, p. 22 — optimal strike price and equilibrium offer strategies
-- statement:
--   Suppose both parties have acquired the other's capability, each privately implementing it either partially ($\Gamma=\gamma$) or fully ($\Gamma=1$), with equal type probabilities. Assume $0<\gamma<1$, $0<V_1$, and $2V_1<V_2$. At a buyout offer price $B$, the recipient accepts or buys out the offeror at that same price, accepting at indifference.
--
--   The strike price $B^*=\gamma V_2/2$ maximizes the offeror's prior-weighted expected payoff among all $B\ge0$, for either offeror type. At that price, the following symmetric offer profiles are Bayesian Nash equilibria:
--
--   $$
--   \begin{cases}
--   \sigma(\gamma)=0,\ \sigma(1)=1,&\gamma V_2\le2V_1,\\
--   \sigma(\gamma)=1,\ \sigma(1)=\displaystyle\frac{\gamma V_2-2V_1}{V_2-2V_1},&\gamma V_2>2V_1.
--   \end{cases}
--   $$
--
--   In the second case the offer probability of a full implementer is strictly between zero and one. This characterizes the paper's reciprocal-option offer step when both parties acquired the other's capability.
--
--   **Formalization Note** Price optimality is evaluated against the prior distribution of the offeree's type, following the paper's separation of price and offer decisions. The claimed profiles are equilibria; uniqueness is not asserted. The source model supplies $V_1>0$ through $V_1=3/(8k)$ with $k>0$.
-- source:
--   Taneri & Crama, Turning the Tables in R&D Licensing Contracts, SSRN 3711872 (version of October 15, 2020), p. 22, Proposition 5

import Mathlib
import Definitions.Def_TurnTables_Reciprocal_Model

namespace TurnTables.Reciprocal

theorem proposition_5 (P : Params) (hP : P.Standing) :
    (∀ R : Impl, ∀ B : ℝ, 0 ≤ B →
      offerorPriorPay P R B ≤ offerorPriorPay P R (strikeB P)) ∧
    (P.γ * P.V2 ≤ 2 * P.V1 →
      IsSymBNE P (strikeB P)
        (fun T => match T with | .part => 0 | .full => 1)) ∧
    (2 * P.V1 < P.γ * P.V2 →
      0 < offerProb P ∧ offerProb P < 1 ∧
        IsSymBNE P (strikeB P)
          (fun T => match T with | .part => 1 | .full => offerProb P)) := by sorry

end TurnTables.Reciprocal
