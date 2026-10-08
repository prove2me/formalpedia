-- Prove2me | Theorems.Thm_PriceOfStability_WeightedSingle_theorem6_3
-- name    : PriceOfStability.WeightedSingle.theorem6_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:40:25.079991+00:00
-- url     : https://prove2.me/theorems/33a47e6c-0d00-47a6-8d72-27e5abdc2c56
-- title:
--   Theorem 6.3 — with a common source and sink, best-response dynamics in weighted games converge to a Nash equilibrium
-- statement:
--   Let $D$ be a finite directed multigraph with a source $s$ and a sink $t$, and consider the weighted cost-sharing game in which every player's strategies are the simple $s$–$t$ paths of $D$, player $i$ has weight $w_i\ge 1$, arc $e$ has a fixed cost $c_e\ge 0$, and a player on path $S_i$ pays $\sum_{e\in S_i}\frac{w_i}{W_e}c_e$, where $W_e$ is the total weight of the players using $e$.
--
--   Then:
--
--   1. **Best-response dynamics terminate.** There is no infinite sequence of profiles $S^0,S^1,S^2,\dots$ in which each $S^{n+1}$ arises from $S^n$ by a best-response move (some player switches to a cheapest strategy given the others, strictly lowering its payment).
--   2. **They stop at a Nash equilibrium.** A profile from which no best-response move is possible is a pure Nash equilibrium.
--   3. **Nash equilibria exist.** If $D$ has at least one simple $s$–$t$ path, the game has a pure Nash equilibrium.
--
--   Weighted games with three or more players need not have a pure Nash equilibrium; the theorem singles out the single-commodity network case in which they always do, and in which the natural dynamics find one.
--
--   **Formalization Note.** Item 1 is the well-foundedness of the relation "$S'$ is reached from $S$ by one best-response move", oriented so that $S'$ lies below $S$. Arc costs are only assumed nonnegative, as in the paper's model.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1620 (PDF p. 19), Theorem 6.3

import Mathlib
import Definitions.Def_PriceOfStability_WeightedSingle_Model
import Definitions.Def_PriceOfStability_WeightedSingle_SingleCommodity

namespace PriceOfStability.WeightedSingle

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*,
SIAM J. Comput. 38 (2008), Theorem 6.3, p. 1620 (PDF p. 19): "For any weighted game in which all
players have the same source s and sink t, best response dynamics converge to a Nash
equilibrium, and hence Nash equilibria exist."

Let `D` be a finite directed multigraph with source `s` and sink `t`, let every player's strategy
family be the set of simple `s`–`t` paths, and let the weights satisfy `wᵢ ≥ 1` and the arc costs
`c_e ≥ 0`. Then
1. there is no infinite sequence of best-response moves (the relation "`S'` is reached from `S`
   by one best-response move" is well-founded with `S'` below `S`);
2. a profile from which no best-response move is possible is a Nash equilibrium;
3. if an `s`–`t` path exists, a Nash equilibrium exists.

**Formalization Note.** `WellFounded r` with `r S' S :↔ IsBRMove Γ S S'` says every descending
`r`-chain, i.e. every run of best-response dynamics, is finite. Costs are only assumed
nonnegative, as in Sect. 2 (the proof's milestones assume positive costs). -/
theorem theorem6_3 {V ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hG : (singleCommodityGame D s t w c).IsStandard) :
    WellFounded (fun S' S => IsBRMove (singleCommodityGame D s t w c) S S') ∧
    (∀ S, IsProfile (singleCommodityGame D s t w c) S →
      (¬ ∃ S', IsBRMove (singleCommodityGame D s t w c) S S') →
      IsNash (singleCommodityGame D s t w c) S) ∧
    ((stPaths D s t).Nonempty → ∃ S, IsNash (singleCommodityGame D s t w c) S) := by sorry

end PriceOfStability.WeightedSingle
