-- Prove2me | Theorems.Thm_ParallelLotteries_exists_pos_measure_affordable
-- name    : ParallelLotteries.exists_pos_measure_affordable
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:01.151064+00:00
-- url     : https://prove2.me/theorems/440cd65e-757b-4e65-a616-f73ebe0ba0ee
-- title:
--   Total cost is invariant under trade, so $C(x'(v))\le C(x(v))\le1$ on a set of positive measure (50)
-- statement:
--   Let $n$ items have quantities $\mu\in\mathbb R^n_+$, let the agents have mass $M>0$ and types distributed by a probability measure $\eta$ on $\mathbb R^n$ that is absolutely continuous with respect to Lebesgue measure, and let $k\ge1$. Let $(\Phi,p)$ be a $k$-ticket equilibrium with allocation $x(v)=\chi(\Phi(v),p)$, and let $x'$ be a trade reallocation of $x$. Then, with the cost $C(y)=\frac1k\sum_i y_i/p_i$,
--
--   1. the total cost is invariant under the trade:
--   $$\int C(x(v))\,d\eta=\int C(x'(v))\,d\eta;$$
--   2. the set $V$ of types $v$ with
--   $$C(x'(v))\le C(x(v))\le 1 \tag{50}$$
--   has $\eta(V)>0$.
--
--   On $V$ the traded bundle $x'(v)$ is affordable at the prices $1/(kp_i)$, which is how the proof of Theorem 2 bounds the gain from trade for the agents in $V$.
--
--   Differences from the source:
--   - reading: $C(y)=\frac1k\sum_i y_i/p_i$ → the sum over items with $p_i>0$; reason: the page divides by $p_i$ without comment; when every $p_i>0$ this is (49) verbatim
--   - encoding: strategy profiles, allocations and integrals as printed → $\Phi$ and $x'$ Borel measurable, $p\in[0,1]^n$, $M>0$; reason: the paper's integrals and measures presuppose measurability, and $\eta$ is a measure on the Borel sets of $\mathbb R^n$; $p$ are probabilities and $M$ is a mass of agents
--   - generalization: the standing assumptions of p.5 (positive value for at least one item; every item preferred to the outside option by a positive measure of agents) → not assumed; reason: the argument of (50) does not use them, and an instance of the paper satisfies the Lean hypotheses
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, display before (50) and (50), p.32

import Mathlib
import Definitions.Def_ParallelLotteries_Model
import Definitions.Def_ParallelLotteries_Budget

open MeasureTheory

namespace ParallelLotteries

/-- **A positive-measure set of agents can afford their new bundle** — Arnosti–Randolph,
SSRN 3370605 (preprint), App. D.2, display (50) and the display before it, p.32: "the total cost
of an allocation is invariant under trade reallocation: ∫ C(x(v)) dη = ∫ C(x′(v)) dη. Thus there
exists a subset V with η(V) > 0, such that for all v ∈ V we have C(x′(v)) ≤ C(x(v)) ≤ 1. (50)"

Let `n` items have supplies `μ ∈ ℝⁿ₊`, let the agents have mass `M > 0` and type distribution `η`
(a probability measure on `ℝⁿ`, absolutely continuous with respect to Lebesgue measure), let
`(Φ, p)` be a `k`-ticket equilibrium with allocation `x(v) = χ(Φ(v), p)`, and let `x′` be a trade
reallocation of `x`. Then
1. `∫ C(x(v)) dη = ∫ C(x′(v)) dη`, and
2. the set of types `v` with `C(x′(v)) ≤ C(x(v)) ≤ 1` has positive `η`-measure.

**Formalization Note.** `C` sums over items with `p_i > 0` (see `ParallelLotteries.cost`); the
paper divides by `p_i` without comment. -/
theorem exists_pos_measure_affordable {n k : ℕ} (hk : 1 ≤ k) (μ : Fin n → ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (M : ℝ) (hM : 0 < M) (η : Measure (Fin n → ℝ))
    [IsProbabilityMeasure η] (hη : η ≪ volume) (Φ : (Fin n → ℝ) → Strategy n k)
    (p : Fin n → ℝ) (heq : IsEquilibrium M μ η Φ p) (x' : (Fin n → ℝ) → Fin n → ℝ)
    (hx' : IsTradeReallocation M μ η (eqAllocation Φ p) x') :
    (∫ v, cost k p (eqAllocation Φ p v) ∂η = ∫ v, cost k p (x' v) ∂η) ∧
    0 < η {v | cost k p (x' v) ≤ cost k p (eqAllocation Φ p v) ∧
      cost k p (eqAllocation Φ p v) ≤ 1} := by sorry

end ParallelLotteries
