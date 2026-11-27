-- Prove2me | Theorems.Thm_SampleMechDesign_Supplement_theorem_5_1
-- name    : SampleMechDesign.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:49:33.967689+00:00
-- url     : https://prove2.me/theorems/ef69c6c2-2a69-5445-a812-0eca77427753
-- title:
--   Theorem 5.1 (corrected: union bound over the partitions of the buyers) — market segmentation $\mathcal M_1\subseteq\dots\subseteq\mathcal M_n$: weighted uniform deviation bound
-- statement:
--   Consider non-anonymous item pricing over additive buyers with nonnegative prices, and the price-group classes $\mathcal M_k$ ($k\in[n]$), each a union over all partitions of the buyers into $k$ groups. Let $w:\mathbb N\to[0,1]$ satisfy $\sum_iw(i)\le1$. Let $\mathcal D$ be a distribution over additive valuation vectors such that the profit of every mechanism lies in $[0,U]$ for $\mathcal D$-almost every valuation vector. For every $N\ge1$ and $\delta\in(0,1)$, with probability greater than $1-\delta$ over $S\sim\mathcal D^N$: for every $k\in[n]$ with $w(k)>0$ and every $M\in\mathcal M_k$,
--   $$
--   |\mathrm{profit}_S(M)-\mathrm{profit}_{\mathcal D}(M)|\ \le\ 360U\sqrt{\frac{km\ln(4knm^2)}{N}}+4U\sqrt{\frac2N\ln\frac{4k^n}{\delta\cdot w(k)}} .
--   $$
--
--   The paper's bound, $360U\sqrt{km\log(4nm)/N}+4U\sqrt{(2/N)\ln(4/(\delta w(k)))}$, is false: its proof treats $\mathcal M_k$ as one $(km,nm)$-delineable class, but $\mathcal M_k$ is a union over partitions. With $m=1$, $n=10^{12}$, zero cost, $\mathcal D$ uniform on the $n$ valuation vectors in which buyer $i$ alone values the item at $3$, $k=2$, $w(i)=2^{-i}$, $\delta=1/2$ and $N=10^{10}$, for every sample the mechanism of $\mathcal M_2$ that charges $2$ to the sampled buyers and $4$ to the others has $\mathrm{profit}_S=2$ and $\mathrm{profit}_{\mathcal D}\le0.02$, while the printed bound is about $0.083$. The corrected bound applies Theorem 3.9 to each fixed partition map $g:[n]\to[k]$, whose class is $(km,nm)$-delineable, with confidence $\delta w(k)/k^n$, and takes a union bound over the $k^n$ maps and over $k$.
--
--   The theorem lets a seller trade the profit of finer market segmentations against their generalization error.
--
--   **Formalization Note** As in the published goal, profits lie in $[0,U]$ on one $\mathcal D$-full set, each profit function of the class (nonnegative prices) is measurable, each fixed-partition class is pointwise measurable, and the probability is the product measure of the bad event (its outer measure if it is not measurable). Levels $k$ with $w(k)=0$, where the printed bound is $+\infty$, are excluded.
--
--   Differences from the source:
--   - correction: 360U√(km log(4nm)/N) + 4U√((2/N) ln(4/(δ·w(k)))) → 360U√(km ln(4knm²)/N) + 4U√((2/N) ln(4kⁿ/(δ·w(k)))); reason: false as printed: M_k is a union over partitions; counterexample m = 1, n = 10¹², zero cost, D uniform on single-buyer valuations 3, k = 2, w(i) = 2^{−i}, δ = 1/2, N = 10¹⁰ (deviation ≈ 1.98 > 0.083 on every sample); the correction is Theorem 3.9 per partition map plus a union bound over the kⁿ maps
--   - correction: U is the maximum profit of any mechanism over the support of D → profits of every mechanism of the class lie in [0, U] on one D-full set; reason: base correction C2: with negative profits the maximum profit does not bound the deviation (fails at N = 1)
--   - correction: no measurability condition → each profit function of the class (nonnegative prices) is measurable and each fixed-partition class is pointwise measurable; reason: base correction C3: Theorem 3.8 is false for arbitrary classes under CH; the route of the proof goes through it
--   - reading: log(4nm) next to ln(4/(δ·w(k))) → natural logarithm in both terms; reason: base reading: the stronger statement
--   - encoding: w(k) = 0 (printed bound +∞) → levels k with w(k) = 0 are excluded; reason: Lean's x / 0 = 0 would turn ln(4/(δ·0)) into 0; only undefined cases are excluded
--   - reading: item prices (sign not stated), arrival order and tie-breaking not specified → nonnegative prices; every arrival order and every tie-breaking rule; reason: with negative prices allowed the [0, U] range hypothesis is never satisfied; the order and ties are arbitrary in the paper
--   - encoding: with probability 1 − δ, the deviation bound holds → the product (outer) measure of the bad event is < δ, for N ≥ 1 and δ ∈ (0, 1); reason: the published goal's convention
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem 5.1, p.17 (PDF p.17); proof p.45; Section 5, pp.16–17

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Definitions.Def_SampleMechDesign_Supplement_itemPricingProfit
import Definitions.Def_SampleMechDesign_Supplement_priceGroupPrices

open MeasureTheory

namespace SampleMechDesign.Supplement

open BartlettBousquetMendelson.LocalRad

/-- **Theorem 5.1, corrected.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, p.17 (proof
p.45). Non-anonymous item pricing over additive buyers, market segmentation into `k` price groups
(`M_k`, a union over all partitions of the buyers), and a weight function `w : ℕ → [0, 1]` with
`∑ w ≤ 1`. For every `N ≥ 1` and `δ ∈ (0, 1)`,

`Pr_{S ∼ D^N}[∃ k ∈ [n] with w(k) > 0, ∃ M ∈ M_k,
  |profit_S(M) − profit_D(M)| > 360 U √(k m ln(4 k n m²)/N) + 4 U √((2/N) ln(4 kⁿ/(δ w(k))))] < δ`.

**Formalization Note.**
* Correction: the paper's bound `360 U √(k m log(4nm)/N) + 4 U √((2/N) ln(4/(δ w(k))))` is false.
  `M_k` is a union over the partitions of the buyers, and the proof treats it as one
  `(km, nm)`-delineable class. Counterexample: `m = 1`, `n = 10¹²`, zero cost, `D` uniform on the
  `n` profiles where buyer `i` alone values the item at `3`, `k = 2`, `w(i) = 2^{-i}`, `δ = 1/2`,
  `N = 10¹⁰`. For every sample the mechanism of `M_2` charging `2` to the sampled buyers and `4` to
  the rest has `profit_S = 2`, `profit_D ≤ 0.02`, while the bound is about `0.083`. The corrected
  bound is Theorem 3.9 for each block map `g : [n] → [k]` (a `(km, nm)`-delineable class), with a
  union bound over the `kⁿ` maps and over `k`.
* As in the published goal: profits lie in `[0, U]` on one `D`-full set (`U` alone fails),
  each profit function of the class (nonnegative prices) is measurable, and each fixed-partition class is pointwise measurable;
  `log` is natural. `w(k) = 0` makes the paper's bound `+∞`, so those `k` are excluded rather than
  letting `x / 0 = 0` shrink the bound.
* Prices are nonnegative; the arrival order `ord` and the tie-breaking rule `tb` are arbitrary. -/
theorem theorem_5_1 {n m : ℕ} (ord : Fin n ≃ Fin n)
    (tb : BVal n m × Fin n → Finset (Finset (Fin m)) → Finset (Fin m)) (htb : IsChoice tb)
    (c : Bundles n m → ℝ)
    (hmeas : ∀ p : Fin n → Fin m → ℝ, (∀ j i, 0 ≤ p j i) →
      Measurable fun v : AVal n m => ipProfit ord tb c p (additiveVal v))
    (hpm : ∀ (k : ℕ) (g : Fin n → Fin k), IsPointwiseMeasurableClass
      {f : AVal n m → ℝ | ∃ p : Fin n → Fin m → ℝ, (∀ j i, 0 ≤ p j i) ∧
        (∀ j j', g j = g j' → p j = p j') ∧ f = fun v => ipProfit ord tb c p (additiveVal v)})
    (D : Measure (AVal n m)) [IsProbabilityMeasure D] {U : ℝ}
    (hU : ∀ᵐ v ∂D, ∀ p : Fin n → Fin m → ℝ, (∀ j i, 0 ≤ p j i) →
      ipProfit ord tb c p (additiveVal v) ∈ Set.Icc 0 U)
    (w : ℕ → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (hwsum : ∀ s : Finset ℕ, ∑ i ∈ s, w i ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Measure.pi (fun _ : Fin N => D)
      {S : Fin N → AVal n m | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧ 0 < w k ∧ ∃ p ∈ priceGroupPrices n m k,
        360 * U * √((k : ℝ) * m * Real.log (4 * (k : ℝ) * n * (m : ℝ) ^ 2) / N) +
            4 * U * √(2 / (N : ℝ) * Real.log (4 * (k : ℝ) ^ n / (δ * w k))) <
          |(1 / (N : ℝ)) * ∑ i, ipProfit ord tb c p (additiveVal (S i)) -
            ∫ v, ipProfit ord tb c p (additiveVal v) ∂D|} < ENNReal.ofReal δ := by sorry

end SampleMechDesign.Supplement
