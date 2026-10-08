-- Prove2me | Theorems.Thm_PriceOfStability_WeightedPotential_join_shared_edge
-- name    : PriceOfStability.WeightedPotential.join_shared_edge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:38:30.663986+00:00
-- url     : https://prove2.me/theorems/28874e34-687f-4601-aabb-77974a0902c6
-- title:
--   Theorem 6.1, proof — joining an edge used by one other player raises $\Phi_e$ by $w_i$ times the new share
-- statement:
--   Let $G$ be a weighted cost-sharing game with weights $w_i \ge 1$ and edge costs $c_e \ge 0$ in which each edge lies in the strategy spaces of at most two players. Let $S$ be a profile and $e$ an edge used in $S$ by exactly one player $j$, and let a player $i \ne j$ switch to a feasible strategy $T$ containing $e$, giving the profile $S' = (S_{-i}, T)$. Then
--
--   $$
--   \Phi_e(S') - \Phi_e(S) = c_e\Bigl(w_i - \frac{w_i w_j}{w_i + w_j}\Bigr) = \frac{c_e\, w_i^2}{w_i + w_j} = w_i \cdot \frac{w_i}{W'_e}\, c_e ,
--   $$
--
--   where $W'_e = w_i + w_j$ is the weight on $e$ in $S'$; that is, the change in the edge potential equals $w_i$ times the cost $i$ incurs on $e$ after joining.
--
--   This is the computation the paper displays in the proof of Theorem 6.1, the basic case of the weighted potential identity.
--
--   **Formalization Note** "The edge already supported another player $j$" is encoded as: the set of users of $e$ in $S$ is exactly $\{j\}$. The conclusion states both the closed form $c_e w_i^2/(w_i+w_j)$ and the form $w_i$ times $i$'s new payment for $e$.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1620 (PDF p. 19), Theorem 6.1, proof, displayed computation

import Mathlib
import Definitions.Def_PriceOfStability_WeightedPotential_Model

namespace PriceOfStability.WeightedPotential

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- Anshelevich et al., SIAM J. Comput. 38 (2008), Theorem 6.1, proof, p. 1620 (PDF p. 19),
displayed computation: "Consider a player i and an edge e that player i joins. If the edge already
supported another player j, then i's cost for using e is c_e w_i/(w_i+w_j), while the change in
Φ_e(S) is c_e(w_i − w_i w_j/(w_i + w_j)) = c_e w_i^2/(w_i + w_j). Thus the change in potential when
i joins e equals the cost i incurs, scaled up by a factor of w_i."

In a standard weighted game in which every edge lies in the strategy spaces of at most two players,
let `S` be a profile in which edge `e` is used by exactly one player `j ≠ i` (so `i` does not use
it), and let `i` switch to a feasible strategy `T ∋ e`. Then the edge potential of `e` rises by
`c_e wᵢ²/(wᵢ + wⱼ)`, which is `wᵢ` times `i`'s payment `(wᵢ/W_e) c_e` for `e` after the switch.

**Formalization Note.** "The edge already supported another player j" and "player i joins e" are
`users S e = {j}` together with `e ∈ T`; the hypotheses of Theorem 6.1 are kept as binders. -/
theorem join_shared_edge (G : WeightedGame ι E) (hG : G.IsStandard)
    (hspace : ∀ e, (Finset.univ.filter (fun i => e ∈ strategySpace G i)).card ≤ 2)
    (S : ι → Finset E) (hS : IsProfile G S) (i j : ι) (hij : i ≠ j)
    (T : Finset E) (hT : T ∈ G.strategies i) (e : E)
    (hjoin : users S e = {j}) (heT : e ∈ T) :
    edgePotential G (Function.update S i T) e - edgePotential G S e
        = G.edgeCost e * G.weight i ^ 2 / (G.weight i + G.weight j) ∧
      edgePotential G (Function.update S i T) e - edgePotential G S e
        = G.weight i * (G.weight i / edgeWeight G (Function.update S i T) e * G.edgeCost e) := by sorry

end PriceOfStability.WeightedPotential
