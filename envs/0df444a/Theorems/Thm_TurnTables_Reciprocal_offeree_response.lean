-- Prove2me | Theorems.Thm_TurnTables_Reciprocal_offeree_response
-- name    : TurnTables.Reciprocal.offeree_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:21.118844+00:00
-- url     : https://prove2.me/theorems/2007ec0c-0d78-4567-8f50-d83667bcc455
-- title:
--   §4.4 and §4.5 — response to an offer at the Proposition 5 strike price
-- statement:
--   Suppose both parties have acquired the other's capability and the parameters satisfy $0<\gamma<1$, $0<V_1$, and $2V_1<V_2$. At the reciprocal-option strike price $B^*=\gamma V_2/2$, a partially implementing offeree accepts the offer at indifference, whereas a fully implementing offeree reciprocates:
--
--   $$
--   \neg\operatorname{Reciprocates}(\gamma,B^*)\quad\text{and}\quad
--   \operatorname{Reciprocates}(1,B^*).
--   $$
--
--   This states the response behind the paper's reallocation claim: a fully capable recipient can take the product from a less capable offeror.
--
--   **Formalization Note** The response is calculated from the offeree's payoff comparison, with acceptance on equality. The standing $V_1>0$ comes from the source model and is not needed for this local comparison.
-- source:
--   Taneri & Crama, Turning the Tables in R&D Licensing Contracts, SSRN 3711872 (version of October 15, 2020), p. 22, §4.4 tie rule; pp. 25–26, §4.5 reallocation paragraph

import Mathlib
import Definitions.Def_TurnTables_Reciprocal_Model

namespace TurnTables.Reciprocal

theorem offeree_response (P : Params) (hP : P.Standing) :
    ¬ Reciprocates P .part (strikeB P) ∧
      Reciprocates P .full (strikeB P) := by sorry

end TurnTables.Reciprocal
