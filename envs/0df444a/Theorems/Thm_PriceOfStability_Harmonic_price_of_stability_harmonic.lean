-- Prove2me | Theorems.Thm_PriceOfStability_Harmonic_price_of_stability_harmonic
-- name    : PriceOfStability.Harmonic.price_of_stability_harmonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:02:19.999768+00:00
-- url     : https://prove2.me/theorems/784920f8-427d-4207-9dcd-59d681eb1e1b
-- title:
--   Theorem 2.1 — the price of stability of the fair connection game is at most H(k), and this is tight
-- statement:
--   Consider the fair connection game: $k$ players, a finite set of edges with nonnegative costs $c_e$, each player $i$ choosing a feasible set of edges $S_i\in\Sigma_i$, and the cost of each edge shared equally by the players using it. The cost of a strategy profile is the total cost $\sum_{e\in\bigcup_i S_i} c_e$ of the edges used.
--
--   1. **Upper bound (Theorem 2.1).** If every player has a feasible strategy, there is a pure Nash equilibrium $S$ with
--   $$\operatorname{cost}(S)\le H(k)\cdot\operatorname{cost}(P)\quad\text{for every strategy profile }P,\qquad H(k)=1+\tfrac12+\dots+\tfrac1k.$$
--   2. **Tightness (Fig. 1.1).** For every $k\ge1$ and $\varepsilon>0$, the instance of Fig. 1.1 has a pure Nash equilibrium, every pure Nash equilibrium of it costs $H(k)$, and some strategy profile costs $1+\varepsilon$; so its price of stability is at least $H(k)/(1+\varepsilon)$, which tends to $H(k)$ as $\varepsilon\to0$.
--
--   The price of stability compares the best Nash equilibrium with the optimum; the price of anarchy of the same game is $k$.
--
--   **Formalization Note.** Strategy families are arbitrary families of edge sets (the paper's *Extensions* paragraph); the directed-graph game is the instance in which $\Sigma_i$ is the family of edge sets connecting player $i$'s terminals. $H(k)$ is Mathlib's `harmonic` cast to $\mathbb R$, $k$ the number of players. The bound is stated as the existence of a good equilibrium, without dividing by the optimum.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1607 (PDF p. 6), Theorem 2.1; p. 1608 (PDF p. 7), tightness remark; p. 1604 (PDF p. 3), Fig. 1.1

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_fig11

open CongestionPoA.AsymSum

namespace PriceOfStability.Harmonic

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*, SIAM J.
Comput. 38 (2008), Theorem 2.1, p. 1607 (PDF p. 6), with its tightness ("Recall from the example in
Figure 1.1 that the upper bound of Theorem 2.1 is tight", p. 1608 (PDF p. 7); Fig. 1.1, p. 1604
(PDF p. 3)).

1. The price of stability of the fair connection game is at most `H(k)`: for every game with
   nonnegative constant edge costs `c_e` in which a profile exists, some pure Nash equilibrium
   `S` has `cost(S) ≤ H(k) · cost(P)` for every profile `P`, `k` the number of players.
2. Tightness: for every `k ≥ 1` and `ε > 0` the instance of Fig. 1.1 has a Nash equilibrium,
   every Nash equilibrium costs `H(k)`, and some profile costs `1 + ε`.

**Formalization Note.** Strategy families are arbitrary families of edge sets (*Extensions*,
p. 1609); the directed-graph game is the instance `Σᵢ = {S ⊆ E : S connects Tᵢ}`. Player and
edge types are quantified in `Type`. `H(k)` is Mathlib's `harmonic` cast to `ℝ`,
`k = Fintype.card ι`. The price of stability is in existence form (never "every equilibrium":
the price of anarchy is `k`), without dividing by the optimum. -/
theorem price_of_stability_harmonic :
    (∀ {ι E : Type} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
      (strategies : ι → Finset (Finset E)) (c : E → ℝ), (∀ e, 0 ≤ c e) →
      (∃ P, IsProfile (fairGame strategies (fun e _ => c e)) P) →
      ∃ S, IsPureNash (fairGame strategies (fun e _ => c e)) S ∧
        ∀ P, IsProfile (fairGame strategies (fun e _ => c e)) P →
          designCost (fun e _ => c e) S ≤
            (harmonic (Fintype.card ι) : ℝ) * designCost (fun e _ => c e) P) ∧
    (∀ (k : ℕ) (ε : ℝ), 1 ≤ k → 0 < ε →
      (∃ S, IsPureNash (fig11 k ε) S) ∧
      (∀ S, IsPureNash (fig11 k ε) S →
        designCost (fun e _ => fig11Cost k ε e) S = (harmonic k : ℝ)) ∧
      ∃ P, IsProfile (fig11 k ε) P ∧ designCost (fun e _ => fig11Cost k ε e) P = 1 + ε) := by sorry

end PriceOfStability.Harmonic
