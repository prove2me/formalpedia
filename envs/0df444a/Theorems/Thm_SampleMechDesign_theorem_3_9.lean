-- Prove2me | Theorems.Thm_SampleMechDesign_theorem_3_9
-- name    : SampleMechDesign.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:12:15.811375+00:00
-- url     : https://prove2.me/theorems/4b80ad3a-e71a-4642-a14e-3d4f291f3cd9
-- title:
--   Theorem 3.9, p.11 — generalization guarantee for $(d,t)$-delineable classes (corrected: affine on arrangement cells, profits in $[0,U]$, pointwise-measurable class)
-- statement:
--   This is the main theorem of the paper. Let $\mathcal M=\{\mathrm{profit}_p:p\in P\}$, $P\subseteq\mathbb R^d$, $d,t\ge1$, be a $(d,t)$-delineable, pointwise measurable class of measurable functions on a measurable space $X$ of valuations. Let $D$ be a probability measure on $X$ and $U$ a real number such that, on one set of full $D$-measure, $0\le\mathrm{profit}_p\le U$ for every $p\in P$. Then for every $N\ge1$ and $\delta\in(0,1)$,
--
--   $$
--   \Pr_{S\sim D^N}\Bigl[\exists p\in P:\ \Bigl|\tfrac1N\sum_{i=1}^N \mathrm{profit}_p(S_i)-\mathbb E_{v\sim D}[\mathrm{profit}_p(v)]\Bigr|>120U\sqrt{\tfrac{9d\ln(4dt)}N}+4U\sqrt{\tfrac{2\ln(4/\delta)}N}\Bigr]<\delta.
--   $$
--
--   With high probability over $N$ samples, every mechanism of the class has average profit on the samples close to its expected profit, so a mechanism chosen on the samples performs nearly as well on the distribution. The bound depends on the class only through $d$ and $t$, and the paper derives its sample complexity results for pricing and auction classes from it.
--
--   Differences from the source:
--   - correction: profit_v linear on every connected component of P \ H (Definition 3.5) → IsDelineable: at most t hyperplanes (a ≠ 0) and one affine function on P ∩ C for every sign-vector cell C, faces included; reason: the printed definition makes the result false. P = ℕ ⊆ ℝ has singleton components, so every class indexed by ℕ is delineable and the class of complements of finite subsets of ℕ has infinite pseudo-dimension. P = ℝ² with profit carried on a hyperplane fails the same way
--   - correction: U is the maximum profit over the support of D → profits in [0, U]; reason: a negative profit breaks the bound: P = {0}, X = {0, 1}, D uniform, profit(0) = 0, profit(1) = -2 has maximum U = 0 and deviation 1 at N = 1. The paper itself uses the range [0, U_i] in Corollary 4.3, p.16
--   - correction: any (d, t)-delineable class → IsPointwiseMeasurableClass (profit image of P), the hypothesis of Theorem 3.8; reason: the paper proves Theorem 3.9 from Theorem 3.8, which as cited from Pollard needs a measurability condition on the class (Pollard's permissibility; the paper names none), and without one the outer-measure bound is false in ZFC. Pointwise measurability is the standard form of that condition, the one Theorem 3.8 carries here; it excludes some jointly measurable classes, e.g. profit_p(v) = 1[p₁ + p₂ = v]. Take d = t = 1, U = 1, D Lebesgue on [0,1], N with ε(N, 1/2) < 1, and, by transfinite recursion over the closed sets of positive measure in [0,1]^N, disjoint N-element blocks such that same-block tuples meet each such set. The indicators of the blocks are measurable, null, and (1,1)-delineable, and the event has outer measure 1
--   - reading: log in 9d log(4dt) → Real.log, the natural logarithm; reason: the base is not pinned. The display also writes ln, while Lemma A.3 is the natural-log lemma of Shalev-Shwartz and Ben-David. The natural logarithm is the stronger reading and it holds by a face count of the arrangement (paper notes)
--   - reading: a generalization guarantee, which by Definition 3.1 holds for every distribution with one function ϵ → for each D, a bound with a U valid for that D; reason: in the theorem U is defined from D, so ϵ depends on D, as in Definition 4.1, p.15
--   - generalization: X the vectors of buyer values for bundles → an arbitrary measurable space X; reason: the statement uses only X, D and the profit; the paper's X is one instance
--   - generalization: U the maximum over the support of D → any real U with the range in [0, U] on one D-full set, uniformly over the class; reason: the bound increases in U, and the support has full measure on the paper's finite-dimensional X, so the printed U is an instance
--   - encoding: d and t unrestricted → 1 ≤ d and 1 ≤ t; reason: log(4dt) is undefined otherwise; this only excludes undefined cases
--   - encoding: measurability of each profit function left implicit → Measurable (profit p) for p ∈ P; reason: the expectation is undefined otherwise
--   - encoding: S ∼ D^N, Pr[...] of the event → S : Fin N → X under Measure.pi, the measure of the set; reason: on a measurable event these agree; on a non-measurable one Lean gives the outer measure, which is at least as strong
--   - encoding: a set of t hyperplanes, linear → at most t hyperplanes, affine; reason: adding hyperplanes refines cells, so at most and exactly agree for t ≥ 1; the proof of Lemma 3.10 writes profit = a·p + b
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem 3.9, p.11 (PDF p.11); Definition 3.1, p.8; Definition 3.5, p.10

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Definitions.Def_SampleMechDesign_IsDelineable

open MeasureTheory

namespace SampleMechDesign

open BartlettBousquetMendelson.LocalRad

/-- **Theorem 3.9, the main theorem, corrected.** Balcan, Sandholm, Vitercik,
arXiv:1705.00243v6, p.11. For a `(d, t)`-delineable pointwise measurable class with profits in
`[0, U]` on one `D`-full set,
`Pr_{S ∼ D^N}[∃ p ∈ P, |(1/N) ∑ profit_p(S i) - E_D profit_p| >
120 U √(9 d ln(4 d t)/N) + 4 U √(2 ln(4/δ)/N)] < δ`.

**Formalization Note.** Corrections: `IsDelineable` works on arrangement cells (Definition 3.5 is
false as printed), profits are nonnegative (`U` alone fails at `N = 1`), and the class is pointwise
measurable. That last hypothesis is forced: the event is measured by `Measure.pi`, i.e. by its outer
measure if it is not measurable, and with only `∀ p ∈ P, Measurable (profit p)` the bound is false in
ZFC (take `d = t = 1`, `U = 1`, `D` Lebesgue on `[0, 1]`, a partition of `[0, 1]` into `N`-element
blocks whose same-block tuples meet every closed set of positive measure in `[0, 1]^N`, built by
transfinite recursion, and `profit_p` the indicator of the `p`-th block). `log` is natural,
`d, t ≥ 1` exclude `log 0`, and `U` is any bound on the profits, so `U` depends on `D`, as in the
theorem and unlike Definition 3.1. -/
theorem theorem_3_9 {X : Type*} [MeasurableSpace X] {d t : ℕ} (hd : 1 ≤ d) (ht : 1 ≤ t)
    {P : Set (Fin d → ℝ)} {profit : (Fin d → ℝ) → X → ℝ} (hdel : IsDelineable d t P profit)
    (hmeas : ∀ p ∈ P, Measurable (profit p)) (hpm : IsPointwiseMeasurableClass (profit '' P))
    (D : Measure X) [IsProbabilityMeasure D] {U : ℝ}
    (hU : ∀ᵐ v ∂D, ∀ p ∈ P, profit p v ∈ Set.Icc 0 U)
    {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Measure.pi (fun _ : Fin N => D)
      {S : Fin N → X | ∃ p ∈ P,
        120 * U * √(9 * (d : ℝ) * Real.log (4 * (d : ℝ) * (t : ℝ)) / (N : ℝ)) +
            4 * U * √(2 * Real.log (4 / δ) / (N : ℝ)) <
          |(1 / (N : ℝ)) * ∑ i, profit p (S i) - ∫ v, profit p v ∂D|} <
      ENNReal.ofReal δ := by sorry

end SampleMechDesign
