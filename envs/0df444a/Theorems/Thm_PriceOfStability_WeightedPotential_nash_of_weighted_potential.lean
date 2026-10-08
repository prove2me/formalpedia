-- Prove2me | Theorems.Thm_PriceOfStability_WeightedPotential_nash_of_weighted_potential
-- name    : PriceOfStability.WeightedPotential.nash_of_weighted_potential
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:39:10.223236+00:00
-- url     : https://prove2.me/theorems/600106de-5255-482d-941c-4a062d8c5328
-- title:
--   Theorem 6.1, proof — a weighted potential yields a pure Nash equilibrium
-- statement:
--   Let $G$ be a weighted cost-sharing game with positive weights $w_i > 0$ in which every player has at least one feasible strategy. Suppose a real function $\Phi$ on profiles satisfies, for every profile $S$, every player $i$ and every $T \in \Sigma_i$,
--
--   $$
--   \Phi(S_{-i}, T) - \Phi(S) = w_i\,\bigl(C_i(S_{-i}, T) - C_i(S)\bigr).
--   $$
--
--   Then $G$ has a pure Nash equilibrium.
--
--   This is the step of the proof of Theorem 6.1 that turns the weighted potential into the existence of an equilibrium.
--
--   **Formalization Note** Only positivity of the weights is assumed (the paper's $w_i \ge 1$ implies it) and no restriction on strategy spaces. Nonempty strategy sets are the implicit condition that a profile exists.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1620 (PDF p. 19), Theorem 6.1, proof

import Mathlib
import Definitions.Def_PriceOfStability_WeightedPotential_Model

namespace PriceOfStability.WeightedPotential

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- Anshelevich et al., SIAM J. Comput. 38 (2008), Theorem 6.1, proof, p. 1620 (PDF p. 19):
"This means that improving moves always decrease Φ(S), thus proving the theorem."

For any weighted game with positive weights and nonempty strategy sets: if a function `Φ` on
profiles changes, under every unilateral deviation of a player `i` from a profile to a feasible
strategy, by `wᵢ` times the change of `i`'s payment, then the game has a pure Nash equilibrium.

**Formalization Note.** Only `wᵢ > 0` is needed here (the paper's standing `wᵢ ≥ 1` implies it),
and no hypothesis on strategy spaces is assumed: this is the step of the proof that turns the
weighted potential into an equilibrium. Nonemptiness of every strategy set is the implicit
hypothesis that a profile exists at all. -/
theorem nash_of_weighted_potential (G : WeightedGame ι E) (hw : ∀ i, 0 < G.weight i)
    (hne : ∀ i, (G.strategies i).Nonempty) (Φ : (ι → Finset E) → ℝ)
    (hΦ : ∀ S, IsProfile G S → ∀ i, ∀ T ∈ G.strategies i,
      Φ (Function.update S i T) - Φ S
        = G.weight i * (payment G (Function.update S i T) i - payment G S i)) :
    ∃ S, IsNash G S := by sorry

end PriceOfStability.WeightedPotential
