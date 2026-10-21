-- Prove2me | Theorems.Thm_TurnTables_Reciprocal_proposition_5_part_2
-- name    : TurnTables.Reciprocal.proposition_5_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:27.233727+00:00
-- url     : https://prove2.me/theorems/60d6640d-9cfa-4d97-a3d7-d49e65b052ce
-- title:
--   Proposition 5 part 2, p. 22 — partial implementers offer and full implementers mix
-- statement:
--   Suppose both parties acquired the other's capability, $0<\gamma<1$, $0<V_1$, $2V_1<V_2$, and $\gamma V_2>2V_1$. Set
--
--   $$
--   \pi=\frac{\gamma V_2-2V_1}{V_2-2V_1}.
--   $$
--
--   Then $0<\pi<1$, and the symmetric profile $\sigma(\gamma)=1$, $\sigma(1)=\pi$ is a Bayesian Nash equilibrium of the reciprocal-option offer game at $B^*=\gamma V_2/2$. A partially implementing party always offers; a fully implementing party offers with probability $\pi$.
--
--   This is Proposition 5's genuine mixed-strategy case.
--
--   **Formalization Note** The equilibrium tests all feasible unilateral offer probabilities. The strike price is evaluated separately against the offeree's prior, and $V_1>0$ follows from the source model.
-- source:
--   Taneri & Crama, Turning the Tables in R&D Licensing Contracts, SSRN 3711872 (version of October 15, 2020), p. 22, Proposition 5 part 2

import Mathlib
import Definitions.Def_TurnTables_Reciprocal_Model

namespace TurnTables.Reciprocal

theorem proposition_5_part_2 (P : Params) (hP : P.Standing)
    (hcase : 2 * P.V1 < P.γ * P.V2) :
    0 < offerProb P ∧ offerProb P < 1 ∧
      IsSymBNE P (strikeB P)
        (fun T => match T with | .part => 1 | .full => offerProb P) := by sorry

end TurnTables.Reciprocal
