-- Prove2me | Theorems.Thm_PriceOfStability_WeightedPotential_potential_change
-- name    : PriceOfStability.WeightedPotential.potential_change
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:38:59.799373+00:00
-- url     : https://prove2.me/theorems/8226b650-ce8b-45d3-98f3-a5d1f62e727a
-- title:
--   Theorem 6.1, proof — when player $i$ moves, $\Delta\Phi = w_i\,\Delta C_i$
-- statement:
--   Let $G$ be a weighted cost-sharing game with weights $w_i \ge 1$ and edge costs $c_e \ge 0$ in which each edge lies in the strategy spaces of at most two players, and let $\Phi$ be the potential of Theorem 6.1. For every profile $S$, every player $i$ and every feasible strategy $T \in \Sigma_i$,
--
--   $$
--   \Phi(S_{-i}, T) - \Phi(S) = w_i\,\bigl(C_i(S_{-i}, T) - C_i(S)\bigr).
--   $$
--
--   The change in the potential under any unilateral move is the mover's change in payment scaled by its weight: $\Phi$ is a weighted potential for the game, which is the heart of Theorem 6.1.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1620 (PDF p. 19), Theorem 6.1, proof

import Mathlib
import Definitions.Def_PriceOfStability_WeightedPotential_Model

namespace PriceOfStability.WeightedPotential

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- Anshelevich et al., SIAM J. Comput. 38 (2008), Theorem 6.1, proof, p. 1620 (PDF p. 19):
"In fact, it is easy to show the more general fact that when player i moves, the change in Φ(S) is
equal to the change in player i's payments scaled up by w_i."

In a standard weighted game in which every edge lies in the strategy spaces of at most two
players, for every profile `S`, every player `i` and every feasible strategy `T` of `i`,
`Φ(S₋ᵢ, T) − Φ(S) = wᵢ · (payment of i at (S₋ᵢ, T) − payment of i at S)`, where `Φ` is the
explicit potential `potential G` of the proof.

**Formalization Note.** The identity is asserted for unilateral deviations from profiles to feasible
strategies, where the strategy-space hypothesis guarantees at most two users per edge. -/
theorem potential_change (G : WeightedGame ι E) (hG : G.IsStandard)
    (hspace : ∀ e, (Finset.univ.filter (fun i => e ∈ strategySpace G i)).card ≤ 2)
    (S : ι → Finset E) (hS : IsProfile G S) (i : ι) (T : Finset E) (hT : T ∈ G.strategies i) :
    potential G (Function.update S i T) - potential G S
      = G.weight i * (payment G (Function.update S i T) i - payment G S i) := by sorry

end PriceOfStability.WeightedPotential
