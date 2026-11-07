-- Prove2me | Theorems.Thm_RGMISFast_lemma_5_2
-- name    : RGMISFast.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:08.275712+00:00
-- url     : https://prove2.me/theorems/ba4e6af9-914e-4dbf-96e7-35fcd24c8eb1
-- title:
--   Lemma 5.2: expected number of active root-connected sets, $E[Y_k(t)]\le(e/t)^k$
-- statement:
--   Let $G$ be a finite simple graph with root $u^*$ and i.i.d. Exp(1) ranks. For every $t>0$ and every integer $k\ge0$,
--   $$
--   \mathbb E[Y_k(t)]\le\Big(\frac et\Big)^k, \tag{19}
--   $$
--   where $Y_k(t)$ is the number of root-connected sets active at time $t$ with exactly $k$ vertices other than $u^*$.
--
--   The bound replaces the worst-case count $(e\Delta)^k$ of root-connected sets by $(e/t)^k$; it holds on every finite simple graph.
--
--   **Formalization Note** The expectation is the Lebesgue integral of $Y_k(t)$ under the product Exp(1) law, stated together with the measurability of $Y_k(t)$.
--
--   Differences from the source:
--   - generalization: E[Y_k(t)] ≤ (e/t)^k → measurability of Y_k(t), and its lower Lebesgue integral ≤ (e/t)^k; reason: the added measurability clause is true and makes the lower integral the expectation; dropping it gives (19)
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Lemma 5.2, eq. (19), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_RGMISFast_Y
import Definitions.Def_RGMISFast_rankLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Lemma 5.2 (Expected Number of Active Root-Connected Sets; Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.18): for every `t > 0` and
every integer `k ≥ 0`, `E[Y_k(t)] ≤ (e/t)^k` (19).

**Formalization Note** Every finite simple graph and every root, no degree bound. The expectation
is the lower Lebesgue integral of `Y_k(t)` under the i.i.d. Exp(1) rank law, plus a measurability
clause. -/
theorem lemma_5_2 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) (t : ℝ) (ht : 0 < t) (k : ℕ) :
    Measurable (fun r : V → ℝ => Y G u k t r) ∧
    ∫⁻ r, (Y G u k t r : ℝ≥0∞) ∂(rankLaw V) ≤ ENNReal.ofReal ((Real.exp 1 / t) ^ k) := by sorry

end RGMISFast
