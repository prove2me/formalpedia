-- Prove2me | Theorems.Thm_PriceOfStability_Undirected_two_player_price_of_stability
-- name    : PriceOfStability.Undirected.two_player_price_of_stability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:40:15.940559+00:00
-- url     : https://prove2.me/theorems/8a0d4b6a-e884-4c5e-ac6c-8801624942eb
-- title:
--   Claim 4.1 — two players with a common terminal in an undirected graph: price of stability ≤ 4/3, tight
-- statement:
--   **Claim 4.1** (Anshelevich et al.). *The price of stability is at most $4/3$ in a fair connection game with two players in an undirected graph, each having two terminals with one terminal in common.* The bound is tight.
--
--   Let $G=(V,E)$ be a finite undirected graph with edge costs $c_e\ge0$, a common terminal $s$ and personal terminals $t_1,t_2$; player $i$ chooses a set of edges $S_i$ connecting $t_i$ with $s$ and the users of an edge share its cost equally. Write $\mathrm{cost}(S)=\sum_{e\in S_1\cup S_2}c_e$.
--
--   1. If some profile exists, there is a pure Nash equilibrium $S$ such that for every profile $P$
--   $$\mathrm{cost}(S)\ \le\ \tfrac43\,\mathrm{cost}(P).$$
--   2. For every $0<\varepsilon<1$, in the 3-node example of Section 4 (edges $(s,t_1),(s,t_2)$ of cost $2$, edge $(t_1,t_2)$ of cost $1+\varepsilon$) the cheapest pure Nash equilibrium costs exactly $4$ and the optimal profile costs exactly $3+\varepsilon$.
--
--   The paper combines (4.1) and (4.2) as
--   $$3y_1+3y_2+3y_3\le 3y_1+3y_2+4y_3=\tfrac13(y_1+y_2)+\tfrac83\big(y_1+y_2+\tfrac32y_3\big)\le\tfrac43(x_1+x_2)+\tfrac83\big(x_1+x_2+\tfrac32x_3\big)=4x_1+4x_2+4x_3.$$
--   For two players this improves the general bound $H(2)=3/2$ of Theorem 2.1.
--
--   **Formalization Note.** "Price of stability at most $4/3$" is stated in existence form, without dividing by the optimum. Strategies are arbitrary connecting edge sets of $G$; players $1,2$ are `0`, `1`.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1613 (PDF p. 12), Claim 4.1 and the example before it; final display p. 1614 (PDF p. 13)

import Definitions.Def_PriceOfStability_Undirected_ThreeNode
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

/-- Claim 4.1 and its tightness example (Anshelevich et al., SIAM J. Comput. 38 (2008), Sect. 4,
p. 1613, PDF p. 12): "The price of stability is at most 4/3 in a fair connection game with two
players in an undirected graph, each having two terminals with one terminal in common", and the
3-node example shows the bound is tight.

1. For every finite undirected graph with nonnegative edge costs, common terminal `s` and personal
   terminals `t₁, t₂` that admits a profile, some pure Nash equilibrium `S` satisfies
   `cost(S) ≤ (4/3)·cost(P)` for every profile `P`.
2. For `0 < ε < 1`, in the 3-node example the cheapest Nash equilibrium costs `4` and the optimum
   costs `3 + ε`.

**Formalization Note.** "Price of stability ≤ 4/3" is stated in existence form (no division by the
optimum). `cost(S)` is the total cost of the edges used by at least one player. Players `0`, `1` are
the paper's 1, 2; strategies are arbitrary connecting edge sets of `G`. -/
theorem two_player_price_of_stability :
    (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Sym2 V → ℝ) (s : V)
        (t : Fin 2 → V), (∀ e, 0 ≤ c e) →
        (∃ P, IsProfile (twoPlayerGame G c s t) P) →
        ∃ S, IsPureNash (twoPlayerGame G c s t) S ∧
          ∀ P, IsProfile (twoPlayerGame G c s t) P →
            PriceOfStability.Harmonic.designCost (fun e _ => c e) S ≤ 4 / 3 * PriceOfStability.Harmonic.designCost (fun e _ => c e) P) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 →
      (∃ S, IsPureNash (threeNode ε) S ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S = 4) ∧
      (∀ S, IsPureNash (threeNode ε) S → 4 ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) S) ∧
      (∃ P, IsProfile (threeNode ε) P ∧ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P = 3 + ε) ∧
      (∀ P, IsProfile (threeNode ε) P → 3 + ε ≤ PriceOfStability.Harmonic.designCost (fun e _ => threeNodeCost ε e) P)) := by sorry

end PriceOfStability.Undirected
