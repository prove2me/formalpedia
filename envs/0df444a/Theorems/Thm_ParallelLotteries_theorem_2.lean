-- Prove2me | Theorems.Thm_ParallelLotteries_theorem_2
-- name    : ParallelLotteries.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:03.100468+00:00
-- url     : https://prove2.me/theorems/d9c5dfcb-bf44-4188-85cc-ea9aa5e7952b
-- title:
--   Theorem 2: every $k$-ticket lottery equilibrium allocation is $(2-1/k)$-trade efficient (corrected: $k=1$)
-- statement:
--   There are $n$ types of items with quantities $\mu\in\mathbb R^n_+$ and a mass $M>0$ of unit-demand agents. An agent's type $v\in\mathbb R^n$ lists her values for the items (the outside option is worth $0$); types are distributed according to a probability measure $\eta$ on $\mathbb R^n$ that is absolutely continuous with respect to Lebesgue measure, and almost every type has a positive value for some item in positive supply. In the $k$-ticket lottery ($k\ge1$) each agent enters at most $k$ tickets into the per-item lotteries and submits a ranking of the items; she receives her most preferred item among those for which one of her tickets is drawn.
--
--   Let $(\Phi,p)$ be a $k$-ticket equilibrium (Definition 3) with allocation $x(v)=\chi(\Phi(v),p)$, and let $x'$ be any trade reallocation of $x$ (a feasible allocation with $\int x'\,d\eta=\int x\,d\eta$, Definition 7). Then:
--
--   1. if $k\ge2$, the set of types $v$ with
--   $$x'(v)\cdot v<\Bigl(2-\frac1k\Bigr)\,x(v)\cdot v$$
--   has positive $\eta$-measure; in particular no trade reallocation multiplies the welfare of every type (or of almost every type) by $2-1/k$ or more, i.e. $x$ is $(2-\frac1k)$-trade efficient in the sense of Definition 9;
--   2. if $k=1$, the set of types $v$ with $x'(v)\cdot v\le x(v)\cdot v$ has positive $\eta$-measure: no trade reallocation makes almost every agent strictly better off.
--
--   Ex-ante trades of probability shares can therefore improve a $k$-ticket lottery outcome, but never uniformly by a factor $2-1/k$ or more (less than $2$ for every $k$).
--
--   Differences from the source:
--   - correction: at $k=1$, "(2−1/k)-trade efficient" (Definition 9 with $\alpha=1$; no trade reallocation $x'$ with $x'(v)\cdot v/x(v)\cdot v\ge1$ for all $v$) → no trade reallocation with $x'(v)\cdot v>x(v)\cdot v$ for almost all $v$; reason: $x'=x$ is always a trade reallocation of $x$ with ratio $1\ge1$; e.g. $n=1$, $\mu_1=1$, $M=1$, $\eta$ uniform on $[1,2]$, all $k=1$ tickets on item 1 for $v_1\ge0$, $p_1=1$ is an equilibrium with $x\equiv1$ that is not $1$-trade efficient as printed
--   - generalization: "there does not exist a trade reallocation $x'$ such that for all $v$" the ratio is $\ge2-1/k$ → the set where it fails has positive $\eta$-measure (no $x'$ achieves it for $\eta$-almost all $v$); reason: it implies the printed statement, and allocations are determined only up to $\eta$-null sets
--   - reading: "we consider only agent types with positive value for at least one item" (p.5) → for $\eta$-almost every $v$ there is an item $i$ with $\mu_i>0$ and $v_i>0$; reason: the ratio $x'(v)\cdot v/x(v)\cdot v$ must be defined; the literal sentence admits $n=1$, $\mu_1=0$, where every consistent $p$ gives $x=x'=0$ a.e. and the ratio is $0/0$
--   - encoding: the ratio condition $x'(v)\cdot v/x(v)\cdot v\ge\alpha$ → $x'(v)\cdot v\ge\alpha\,x(v)\cdot v$; reason: equivalent wherever the ratio is defined, which is $\eta$-almost everywhere by the previous item
--   - encoding: the model as printed → $M>0$, $p\in[0,1]^n$, $\Phi$ and $x'$ Borel measurable, items `Fin n`, types `Fin n → ℝ` with Lebesgue measure, rankings as permutations, $\int x\,d\eta=\int x'\,d\eta$ componentwise; reason: $M$ is a mass of agents, $p$ are probabilities, the paper's integrals presuppose measurability, and $\eta$ is a measure on the Borel sets of $\mathbb R^n$
--   - generalization: "items which a positive measure of agents prefer to their outside option" (p.5) → not assumed; reason: the theorem then covers more markets, and every market of the paper is among them
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), Theorem 2 and Definition 9, p.11 (Definition 7, p.10; model §3, pp.5–8; proof App. D.2, pp.31–35)

import Mathlib
import Definitions.Def_ParallelLotteries_Model

open MeasureTheory

namespace ParallelLotteries

/-- **Theorem 2 (k-ticket equilibria are (2 − 1/k)-trade efficient)** — Arnosti–Randolph,
*Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient*, SSRN 3370605
(preprint), §5.1, p.11 (proof App. D.2, pp.31–35): "Theorem 2. Any equilibrium allocation of the
k-ticket lottery is (2 − 1/k)-trade efficient." Definition 9 (p.11): "Given α ≥ 1, an allocation
x is α-trade efficient if there does not exist a trade reallocation x′ of x such that for all v,
x′(v) · v / x(v) · v ≥ α."

Setting (§3, p.5): `n` items with quantities `μ ∈ ℝⁿ₊`, agents of mass `M > 0` with types
`v ∈ ℝⁿ` distributed by a probability measure `η` absolutely continuous with respect to Lebesgue
measure, outside option `0`. Every type a.e. has a positive value for some item in positive supply
(`hpos`). Let `k ≥ 1`, let `(Φ, p)` be a `k`-ticket equilibrium with allocation
`x(v) = χ(Φ(v), p)`, and let `x′` be any trade reallocation of `x`. Then:
* if `k ≥ 2`: the set of types `v` with `x′(v) · v < (2 − 1/k) · x(v) · v` has positive
  `η`-measure (so no trade reallocation achieves the ratio `≥ 2 − 1/k` for all, or even for
  almost all, `v`);
* if `k = 1`: the set of types `v` with `x′(v) · v ≤ x(v) · v` has positive `η`-measure (no trade
  reallocation makes almost every agent strictly better off).

**Formalization Note.**
1. *Correction at `k = 1`.* Definition 9 with `α = 2 − 1/1 = 1` cannot hold for any allocation:
   `x′ = x` is a trade reallocation of `x` with ratio `1 ≥ 1` everywhere. The `k = 1` clause is
   Definition 9 with a strict `> α`.
2. The ratio `x′(v)·v / x(v)·v ≥ α` is written multiplicatively; `hpos` (the p.5 standing
   sentence "we consider only agent types with positive value for at least one item", read on
   items in positive supply) makes `x(v) · v > 0` for a.e. `v`, so the ratio is defined a.e.
3. The negation of "for all `v`" is taken in the stronger a.e. form (positive measure).
4. Items are `Fin n`, types `Fin n → ℝ` with Lebesgue measure `volume`; see
   `ParallelLotteries.IsEquilibrium` and `ParallelLotteries.IsTradeReallocation`. -/
theorem theorem_2 {n k : ℕ} (hk : 1 ≤ k) (μ : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) (M : ℝ)
    (hM : 0 < M) (η : Measure (Fin n → ℝ)) [IsProbabilityMeasure η] (hη : η ≪ volume)
    (hpos : ∀ᵐ v ∂η, ∃ i, 0 < μ i ∧ 0 < v i)
    (Φ : (Fin n → ℝ) → Strategy n k) (p : Fin n → ℝ) (heq : IsEquilibrium M μ η Φ p)
    (x' : (Fin n → ℝ) → Fin n → ℝ) (hx' : IsTradeReallocation M μ η (eqAllocation Φ p) x') :
    (2 ≤ k → 0 < η {v | ∑ i, x' v i * v i <
        (2 - 1 / (k : ℝ)) * ∑ i, eqAllocation Φ p v i * v i}) ∧
    (k = 1 → 0 < η {v | ∑ i, x' v i * v i ≤ ∑ i, eqAllocation Φ p v i * v i}) := by sorry

end ParallelLotteries
