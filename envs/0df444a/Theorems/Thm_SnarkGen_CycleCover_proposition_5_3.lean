-- Prove2me | Theorems.Thm_SnarkGen_CycleCover_proposition_5_3
-- name    : SnarkGen.CycleCover.proposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:31.402955+00:00
-- url     : https://prove2.me/theorems/078a138b-5a5d-4c4d-a8bc-9a293e43bb1b
-- title:
--   Proposition 5.3 — every 2-regular subgraph of a colourable cubic graph is a colour class of a 4-CDC
-- statement:
--   Let $G$ be a finite simple cubic graph that is colourable (has a proper $3$-edge-colouring), and let $D$ be any $2$-regular subgraph of $G$ (possibly empty, not necessarily spanning). Then $G$ has a $4$-CDC in which $D$ is one of the colour classes: there are even subgraphs $D_0, D_1, D_2, D_3$ of $G$ with
--
--   $$D_0 = D \quad\text{and}\quad \bigl|\{ i : e \in D_i \}\bigr| = 2 \ \text{ for every edge } e \text{ of } G.$$
--
--   The proposition shows that colourable cubic graphs satisfy a strong form of the Strong Cycle Double Cover Conjecture: not only every cycle but every $2$-regular subgraph extends to a CDC. Combined with Lemma 7.2 it gives the $4m/3$ cycle-cover bound.
--
--   **Formalization Note** The $4$-CDC is taken in the "$k$-multiset of even subgraphs" form of `IsKCDCEven`; classes may be empty or repeated.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 15, Proposition 5.3

import Mathlib
import Definitions.Def_SnarkGen_EdgeInsertion_Colourable
import Definitions.Def_SnarkGen_CycleCover_IsTwoRegularEdgeSet
import Definitions.Def_SnarkGen_CycleCover_IsKCDCEven

namespace SnarkGen.CycleCover

/-- arXiv:1206.6690v3, Proposition 5.3 (p. 15): if `G` is a colourable cubic graph and `D` is
any 2-regular subgraph of `G`, then `G` has a 4-CDC in which `D` is one of the colour
classes. -/
theorem proposition_5_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcubic : G.IsRegularOfDegree 3) (hcol : SnarkGen.EdgeInsertion.Colourable G)
    (D : Finset (Sym2 V)) (hD : IsTwoRegularEdgeSet G D) :
    ∃ 𝒟 : Fin 4 → Finset (Sym2 V), IsKCDCEven G 4 𝒟 ∧ 𝒟 0 = D := by sorry

end SnarkGen.CycleCover
