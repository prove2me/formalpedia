-- Prove2me | Theorems.Thm_PriceOfStability_Harmonic_theorem2_3
-- name    : PriceOfStability.Harmonic.theorem2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:40:34.559983+00:00
-- url     : https://prove2.me/theorems/723a5cd7-4a9f-4665-aaa1-0e95f926610b
-- title:
--   Theorem 2.3 — with nondecreasing concave edge costs the price of stability is at most H(k)
-- statement:
--   Consider a fair connection game with $k$ players in which every edge $e$ has a nondecreasing concave cost function $c_e(x)$ of the number $x$ of players using it, with $c_e(0)\ge0$, and the cost of each edge is shared equally by its users. Suppose every player has at least one feasible strategy. Then there is a pure Nash equilibrium $S$ such that
--   $$\operatorname{cost}(S)\le H(k)\cdot\operatorname{cost}(P)\quad\text{for every strategy profile }P,$$
--   where $\operatorname{cost}$ is the cost of the designed network and $H(k)=1+\tfrac12+\dots+\tfrac1k$.
--
--   Concave costs model economies of scale in buying edges shared by many players; constant costs (Theorem 2.1) are the special case.
--
--   **Formalization Note.** Strategy families are arbitrary families of edge sets (the paper's *Extensions* paragraph); the graph game is the instance in which $\Sigma_i$ is the family of edge sets connecting player $i$'s terminals. The price of stability is stated as the existence of a good equilibrium. $c_e(0)\ge0$ is implicit in the paper.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1608 (PDF p. 7), Theorem 2.3

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Theorem 2.3, p. 1608 (PDF p. 7): in a fair connection game in which every edge has a
nondecreasing concave cost function `c_e(x)` of its number of users `x`, the price of stability
is at most `H(k)`: some pure Nash equilibrium `S` has `cost(S) ≤ H(k) · cost(P)` for every
strategy vector `P`.

**Formalization Note.** Strategy families are arbitrary (the *Extensions* paragraph, p. 1609);
the graph game is the instance `Σᵢ = {S ⊆ E : S connects Tᵢ}`. `H(k)` is `harmonic` cast to
`ℝ` with `k = Fintype.card ι`. `c_e(0) ≥ 0` (inside `IsConcaveCost`) is implicit in the paper.
The price of stability is stated in existence form, and a profile is assumed to exist. -/
theorem theorem2_3 {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (strategies : ι → Finset (Finset E)) (c : E → ℕ → ℝ) (hc : IsConcaveCost c)
    (hP : ∃ P, IsProfile (fairGame strategies c) P) :
    ∃ S, IsPureNash (fairGame strategies c) S ∧
      ∀ P, IsProfile (fairGame strategies c) P →
        designCost c S ≤ (harmonic (Fintype.card ι) : ℝ) * designCost c P := by sorry

end PriceOfStability.Harmonic
