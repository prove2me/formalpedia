-- Prove2me | Theorems.Thm_PriceOfStability_WeightedSingle_payment_eq_weight_mul_marginalCost
-- name    : PriceOfStability.WeightedSingle.payment_eq_weight_mul_marginalCost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T20:40:05.533987+00:00
-- url     : https://prove2.me/theorems/2ba32aa9-6b04-43f5-98fb-ec05448fc610
-- title:
--   Theorem 6.3, proof — a player on path $P$ pays $w_i\,c(P)$
-- statement:
--   Consider a weighted game in which all players have the same source $s$ and sink $t$ in a finite directed multigraph, every strategy is a simple $s$–$t$ path, the weights satisfy $w_j\ge 1$ and the arc costs $c_e\ge 0$. For a profile $S$ and a path $P$ let $c_S(P)=\sum_{e\in P} c_e/W_e$ be its marginal cost, $W_e$ being the total weight of the players using $e$ in $S$.
--
--   Then for every profile $S$ and every player $i$,
--   $$\mathrm{pay}_i(S)=w_i\,c_S(S_i).$$
--
--   This identity turns a player's payment into a quantity attached to the path alone, which is what lets the proof of Theorem 6.3 track all paths at once.
--
--   **Formalization Note.** The marginal cost is valued in $[0,+\infty]$, so the identity is stated after embedding the real payment into $[0,+\infty]$; on every arc of $S_i$ one has $W_e\ge w_i\ge 1$, so all terms are finite. Only the standing assumption $c_e\ge 0$ is used.
-- source:
--   Anshelevich et al., The Price of Stability for Network Design with Fair Cost Allocation, SIAM J. Comput. 38 (2008), DOI 10.1137/070680096, p. 1620 (PDF p. 19), Theorem 6.3, proof

import Mathlib
import Definitions.Def_PriceOfStability_WeightedSingle_Model
import Definitions.Def_PriceOfStability_WeightedSingle_SingleCommodity

open scoped ENNReal

namespace PriceOfStability.WeightedSingle

/-- Anshelevich et al., *The Price of Stability for Network Design with Fair Cost Allocation*,
SIAM J. Comput. 38 (2008), Theorem 6.3, proof, p. 1620 (PDF p. 19): "Observe that if player i
currently uses path P, then i's payment is w_i c(P)."

In the weighted single-commodity game with weights `wᵢ ≥ 1` and arc costs `c_e ≥ 0`, for every
strategy profile `S` and every player `i`, the payment of `i` equals `wᵢ · c_S(Sᵢ)`, where
`c_S(P) = Σ_{e∈P} c_e/W_e` is the marginal cost of the path `P` in the state `S`.

**Formalization Note.** `c(P)` is valued in `ℝ≥0∞` (see `marginalCost`), so the identity is stated
after embedding the real payment by `ENNReal.ofReal`; on the arcs of `Sᵢ` every `W_e ≥ wᵢ ≥ 1`, so
all terms are finite. The paper's standing assumption `c_e ≥ 0` (Sect. 2) suffices here; the
positivity of costs that the later steps of the proof need is not assumed. -/
theorem payment_eq_weight_mul_marginalCost {V ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (D : ArcGraph V E) (s t : V) (w : ι → ℝ) (c : E → ℝ)
    (hG : (singleCommodityGame D s t w c).IsStandard)
    (S : ι → Finset E) (hS : IsProfile (singleCommodityGame D s t w c) S) (i : ι) :
    ENNReal.ofReal (payment (singleCommodityGame D s t w c) S i) =
      ENNReal.ofReal (w i) * marginalCost (singleCommodityGame D s t w c) S (S i) := by sorry

end PriceOfStability.WeightedSingle
