-- Prove2me | Theorems.Thm_PriceOfStability_WeightedPotential_theorem6_1
-- name    : PriceOfStability.WeightedPotential.theorem6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:39:25.497653+00:00
-- url     : https://prove2.me/theorems/3f6d525b-1617-401d-b17e-a5a5f98abf45
-- title:
--   Theorem 6.1 — weighted games with each edge in at most two strategy spaces have a potential and a Nash equilibrium
-- statement:
--   Let $G$ be a weighted cost-sharing game with weights $w_i \ge 1$ and edge costs $c_e \ge 0$ in which each edge lies in the strategy spaces of at most two players. Then:
--
--   1. there is a function $\Phi$ on profiles such that, for every profile $S$, every player $i$ and every $T \in \Sigma_i$,
--   $$
--   \Phi(S_{-i}, T) - \Phi(S) = w_i\,\bigl(C_i(S_{-i}, T) - C_i(S)\bigr);
--   $$
--   2. if every player has a feasible strategy, $G$ has a pure Nash equilibrium.
--
--   Weighted cost-sharing games need not have pure equilibria in general; this theorem identifies a structural condition, bounded sharing of every resource, under which existence is guaranteed.
--
--   **Formalization Note** "Potential function" is the weighted potential the paper's proof constructs: the change of $\Phi$ equals the mover's change in payment scaled by its weight. Strategies are arbitrary subsets of a finite ground set, as the remark after the proof allows. Nonempty strategy sets are the implicit condition that a profile exists.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1619 (PDF p. 18), Theorem 6.1, with the remark on the generalized model, p. 1620 (PDF p. 19)

import Mathlib
import Definitions.Def_PriceOfStability_WeightedPotential_Model

namespace PriceOfStability.WeightedPotential

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- Anshelevich et al., SIAM J. Comput. 38 (2008), Theorem 6.1, p. 1619 (PDF p. 18):
"In a weighted game where each edge e is in the strategy spaces of at most two players, there
exists a potential function for this game, and hence a Nash equilibrium exists."

In a weighted game with weights `wᵢ ≥ 1` and costs `c_e ≥ 0` in which every edge lies in the
strategy spaces of at most two players: (1) there is a function `Φ` on profiles such that every
unilateral deviation of a player `i` from a profile to a feasible strategy changes `Φ` by exactly
`wᵢ` times the change of `i`'s payment (the weighted potential of the proof, p. 1620); and (2) if
every player has a feasible strategy, a pure Nash equilibrium exists.

**Formalization Note.** "Potential function" is the weighted potential the proof constructs ("the
change in Φ(S) is equal to the change in player i's payments scaled up by w_i", p. 1620); an exact
potential is not claimed (p. 1619 notes that the unweighted Φ "is not a potential function once
weights are added"). Strategies are arbitrary subsets of a finite ground set, as the remark after
the proof allows; the network game is the instance `Σᵢ = {sᵢ–tᵢ paths}`. Nonempty strategy sets
are the implicit hypothesis that a profile exists. -/
theorem theorem6_1 (G : WeightedGame ι E) (hG : G.IsStandard)
    (hspace : ∀ e, (Finset.univ.filter (fun i => e ∈ strategySpace G i)).card ≤ 2) :
    (∃ Φ : (ι → Finset E) → ℝ, ∀ S, IsProfile G S → ∀ i, ∀ T ∈ G.strategies i,
        Φ (Function.update S i T) - Φ S
          = G.weight i * (payment G (Function.update S i T) i - payment G S i)) ∧
      ((∀ i, (G.strategies i).Nonempty) → ∃ S, IsNash G S) := by sorry

end PriceOfStability.WeightedPotential
