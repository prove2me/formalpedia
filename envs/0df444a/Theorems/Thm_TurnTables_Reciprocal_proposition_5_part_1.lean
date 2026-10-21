-- Prove2me | Theorems.Thm_TurnTables_Reciprocal_proposition_5_part_1
-- name    : TurnTables.Reciprocal.proposition_5_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:20.285462+00:00
-- url     : https://prove2.me/theorems/9566e200-5a04-4b76-88ab-02042f4bce0b
-- title:
--   Proposition 5 part 1, p. 22 — full implementers offer in the low-γV2 regime
-- statement:
--   Suppose both parties acquired the other's capability, $0<\gamma<1$, $0<V_1$, $2V_1<V_2$, and $\gamma V_2\le2V_1$. In the reciprocal-option game at strike price $B^*=\gamma V_2/2$, the symmetric type-contingent profile
--
--   $$
--   \sigma(\gamma)=0,\qquad \sigma(1)=1
--   $$
--
--   is a Bayesian Nash equilibrium: a partially implementing party makes no offer, while a fully implementing party always offers. Each type's prescribed probability maximizes its interim expected payoff over all probabilities in $[0,1]$.
--
--   This is the first offer-strategy case of Proposition 5, including the equality boundary.
--
--   **Formalization Note** The price is fixed at the paper's stated strike price after evaluating it against the offeree's prior. The source model supplies $V_1>0$.
-- source:
--   Taneri & Crama, Turning the Tables in R&D Licensing Contracts, SSRN 3711872 (version of October 15, 2020), p. 22, Proposition 5 part 1

import Mathlib
import Definitions.Def_TurnTables_Reciprocal_Model

namespace TurnTables.Reciprocal

theorem proposition_5_part_1 (P : Params) (hP : P.Standing)
    (hcase : P.γ * P.V2 ≤ 2 * P.V1) :
    IsSymBNE P (strikeB P)
      (fun T => match T with | .part => 0 | .full => 1) := by sorry

end TurnTables.Reciprocal
