-- Prove2me | Theorems.Thm_PriceOfStability_Harmonic_cost_le_potential_le_harmonic
-- name    : PriceOfStability.Harmonic.cost_le_potential_le_harmonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:40:23.129413+00:00
-- url     : https://prove2.me/theorems/6bdb3634-42b2-46a8-a290-6b669de50896
-- title:
--   Theorem 2.3, proof — cost(S) ≤ Φ(S) ≤ H(k)·cost(S) for nondecreasing concave costs
-- statement:
--   Consider the fair cost-sharing game with $k$ players in which every edge $e$ has a cost $c_e(x)$ for $x$ users with $c_e(0)\ge0$, $c_e$ nondecreasing and concave on $\mathbb N$. Let $\Phi(S)=\sum_e\sum_{x=1}^{x_e} c_e(x)/x$ be its Rosenthal potential and $\operatorname{cost}(S)=\sum_{e\in\bigcup_i S_i} c_e(x_e)$ the cost of the designed network. Then for every strategy vector $S$,
--   $$\operatorname{cost}(S)\le\Phi(S)\le H(k)\cdot\operatorname{cost}(S),$$
--   where $H(k)=1+\tfrac12+\dots+\tfrac1k$.
--
--   Together with Theorem 3.1 this gives the $H(k)$ bound on the price of stability.
--
--   **Formalization Note.** $H(k)$ is Mathlib's `harmonic k` cast to $\mathbb R$, with $k$ the number of players. The hypothesis $c_e(0)\ge0$ is implicit in the paper.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1608 (PDF p. 7), Theorem 2.3, proof

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Theorem 2.3, proof, p. 1608 (PDF p. 7): for nondecreasing concave edge costs,
`cost(S) ≤ Φ(S) ≤ H(k) · cost(S)` for all strategies `S`, where `Φ` is the potential (2.1)
of the fair game, `cost(S)` the cost of the designed network and `H(k) = 1 + 1/2 + … + 1/k` with
`k` the number of players.

**Formalization Note.** `H(k)` is Mathlib's `harmonic` (`ℚ`-valued) cast to `ℝ`, with
`k = Fintype.card ι`. The hypothesis `c_e(0) ≥ 0` in `IsConcaveCost` is implicit in the
paper (see that definition). Stated for every strategy vector `S`. -/
theorem cost_le_potential_le_harmonic {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
    [DecidableEq E] (strategies : ι → Finset (Finset E)) (c : E → ℕ → ℝ)
    (hc : IsConcaveCost c) (S : ι → Finset E) :
    designCost c S ≤ potential (fairGame strategies c) S ∧
      potential (fairGame strategies c) S ≤ (harmonic (Fintype.card ι) : ℝ) * designCost c S := by sorry

end PriceOfStability.Harmonic
