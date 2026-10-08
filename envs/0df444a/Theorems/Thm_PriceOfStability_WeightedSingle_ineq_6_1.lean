-- Prove2me | Theorems.Thm_PriceOfStability_WeightedSingle_ineq_6_1
-- name    : PriceOfStability.WeightedSingle.ineq_6_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:40:17.51005+00:00
-- url     : https://prove2.me/theorems/84ff9a23-56ab-4472-b359-f4cbfea5358c
-- title:
--   Theorem 6.3, proof, (6.1) — a best response lowers $\min_{P\in\mathcal P} c(P)$ over the paths meeting $P_1\cup P_2$
-- statement:
--   Consider a weighted game in which all players have the same source $s$ and sink $t$ in a finite directed multigraph, every strategy is a simple $s$–$t$ path, the weights satisfy $w_j\ge 1$ and every arc cost is **strictly positive**. Let $c_S(P)=\sum_{e\in P}c_e/W_e\in[0,+\infty]$ be the marginal cost of $P$ in the state $S$.
--
--   Suppose that player $i$ makes a best-response move from $S$ to $S'$, switching from the path $P_1=S_i$ to the path $P_2=S'_i$, and let $\mathcal P$ be the set of simple $s$–$t$ paths that share an arc with $P_1\cup P_2$. Then
--   $$\min_{P\in\mathcal P} c_{S'}(P)\;<\;\min_{P\in\mathcal P} c_S(P). \tag{6.1}$$
--
--   Paths that share no arc with $P_1\cup P_2$ keep their marginal cost, so (6.1) is the key step of the proof that the sorted tuple of marginal costs strictly decreases.
--
--   **Formalization Note.** Strictly positive costs are an implicit hypothesis of the printed proof: its step "$c_{P'}(P')<c(P')$ unless $P'=P_1$" needs an arc of positive cost in $P'\setminus P_1$, and $c_e/W_e$ is $0/0$ on an unused arc of zero cost. Minima are taken in $[0,+\infty]$; $\mathcal P$ contains $P_1$, so it is nonempty.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1620 (PDF p. 19), Theorem 6.3, proof, (6.1)

import Mathlib
import Definitions.Def_PriceOfStability_WeightedSingle_Model
import Definitions.Def_PriceOfStability_WeightedSingle_SingleCommodity

open scoped ENNReal

namespace PriceOfStability.WeightedSingle

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*,
SIAM J. Comput. 38 (2008), Theorem 6.3, proof, inequality (6.1), p. 1620 (PDF p. 19).

In the weighted single-commodity game with weights `wᵢ ≥ 1` and positive arc costs, suppose that
player `i` makes a best-response move from `S` to `S'`, switching from the path `P₁ = Sᵢ` to the
path `P₂ = S'ᵢ`. Let `𝒫` be the set of simple `s`–`t` paths that share an arc with `P₁ ∪ P₂`.
Then the minimum over `𝒫` of the marginal costs after the move is strictly smaller than the
minimum before it: `min_{P∈𝒫} c_{P₂}(P) < min_{P∈𝒫} c(P)`.

**Formalization Note.** Arc costs are assumed strictly positive (`0 < c e`), an implicit hypothesis
of the printed proof: its step "`c_{P′}(P′) < c(P′)` unless `P′ = P₁`" needs an arc of positive
cost in `P′ \ P₁`, and `c(P) = Σ c_e/W_e` is the undefined `0/0` on an unused zero-cost arc.
Minima are `Finset.inf` in `ℝ≥0∞`; `𝒫` is nonempty because it contains `P₁`. -/
theorem ineq_6_1 {V ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hw : ∀ j, 1 ≤ w j) (hc : ∀ e, 0 < c e)
    (S S' : ι → Finset E) (i : ι) (hmove : IsBRMoveBy (singleCommodityGame D s t w c) i S S') :
    (pathsMeeting (stPaths D s t) (S i ∪ S' i)).inf
        (marginalCost (singleCommodityGame D s t w c) S') <
      (pathsMeeting (stPaths D s t) (S i ∪ S' i)).inf
        (marginalCost (singleCommodityGame D s t w c) S) := by sorry

end PriceOfStability.WeightedSingle
