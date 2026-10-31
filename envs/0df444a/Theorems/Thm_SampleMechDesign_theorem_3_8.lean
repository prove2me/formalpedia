-- Prove2me | Theorems.Thm_SampleMechDesign_theorem_3_8
-- name    : SampleMechDesign.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:11:40.762026+00:00
-- url     : https://prove2.me/theorems/ea296091-71fc-4456-b85e-09c71d13bfee
-- title:
--   Theorem 3.8, p.10 (Pollard, Dudley) — pseudo-dimension generalization bound (corrected: pointwise-measurable class, profits in $[0,U]$)
-- statement:
--   Let $\mathcal F$ be a pointwise measurable class of measurable functions on a measurable space $X$, and let $\mathrm{Pdim}(\mathcal F)\le k$. Let $D$ be a probability measure on $X$ and $U$ a real number such that, on one set of full $D$-measure, $0\le f\le U$ for every $f\in\mathcal F$. Then for every $N\ge1$ and $\delta\in(0,1)$,
--
--   $$
--   \Pr_{S\sim D^N}\Bigl[\exists f\in\mathcal F:\ \Bigl|\tfrac1N\sum_{i=1}^N f(S_i)-\mathbb E_{v\sim D}[f(v)]\Bigr|>120U\sqrt{\tfrac kN}+4U\sqrt{\tfrac{2\ln(4/\delta)}N}\Bigr]<\delta.
--   $$
--
--   This is the uniform convergence bound for pseudo-dimension, stated with explicit constants; it is the probabilistic half of the main theorem.
--
--   Differences from the source:
--   - correction: any mechanism class → IsPointwiseMeasurableClass F; reason: the printed statement fails under CH: for a well-order of [0,1] of type ω₁, the class of initial-segment indicators has VC dimension 1, members of expectation 0, and a member with average 1 on every sample. Pollard assumes permissibility; pointwise measurability is the standard condition (van der Vaart and Wellner, §2.3.3)
--   - correction: U is the maximum profit over the support of D → profits in [0, U]; reason: a negative profit breaks the bound: P = {0}, X = {0, 1}, D uniform, profit(0) = 0, profit(1) = -2 has maximum U = 0 and deviation 1 at N = 1. The paper itself uses the range [0, U_i] in Corollary 4.3, p.16
--   - reading: a generalization guarantee, which by Definition 3.1 holds for every distribution with one function ϵ → for each D, a bound with a U valid for that D; reason: in the theorem U is defined from D, so ϵ depends on D, as in Definition 4.1, p.15
--   - generalization: a mechanism class → a set F of real functions on X; reason: a mechanism class is its set of profit functions
--   - generalization: X the vectors of buyer values for bundles → an arbitrary measurable space X; reason: the statement uses only X, D and the profit; the paper's X is one instance
--   - generalization: U the maximum over the support of D → any real U with the range in [0, U] on one D-full set, uniformly over the class; reason: the bound increases in U, and the support has full measure on the paper's finite-dimensional X, so the printed U is an instance
--   - encoding: 120U √(Pdim(M)/N) → 120 U √(k/N) for a real upper bound k on the pseudo-dimension; reason: the bound increases in k, k = Pdim(M) is an instance, and Pdim = ∞ makes the printed bound empty
--   - encoding: Pdim(M) ≤ k → every shattered m-tuple has m ≤ k; reason: the published Shatters is Definition 3.6 with b the indicator of the complement of T, a tuple with a repeated point is never shattered, and this form also excludes Pdim = ∞
--   - encoding: measurability of each profit function left implicit → Measurable f for f ∈ F; reason: the expectation is undefined otherwise
--   - encoding: S ∼ D^N, Pr[...] of the event → S : Fin N → X under Measure.pi, the measure of the set; reason: on a measurable event these agree; on a non-measurable one Lean gives the outer measure, which is at least as strong
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem 3.8, p.10 (PDF p.10); Definition 3.1, p.8

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass

open MeasureTheory

namespace SampleMechDesign

open FoundationsML.Regression BartlettBousquetMendelson.LocalRad

/-- **Theorem 3.8 (Pollard, Dudley), corrected.** Balcan, Sandholm, Vitercik,
arXiv:1705.00243v6, p.10. For a pointwise measurable class `F` of measurable functions with values
in `[0, U]` on one `D`-full set and `Pdim(F) ≤ k`,
`Pr_{S ∼ D^N}[∃ f ∈ F, |(1/N) ∑ f(S i) - E_D f| > 120 U √(k/N) + 4 U √(2 ln(4/δ)/N)] < δ`.

**Formalization Note.** Corrections: `IsPointwiseMeasurableClass F`, since for an arbitrary class
the statement fails under CH (the well-order class has VC dimension 1); and `0 ≤ f` on the support,
since `U` alone cannot bound a negative profit. The range holds uniformly over `F` on one full set,
not class member by class member. `k` is any real upper bound on the pseudo-dimension: the bound
increases in `k`, and `Pdim = ∞` makes the printed bound empty. A sample is a tuple `S : Fin N → X`.
The event is measured by `Measure.pi`, i.e. by its outer measure if it is not measurable. -/
theorem theorem_3_8 {X : Type*} [MeasurableSpace X] {F : Set (X → ℝ)}
    (hF : ∀ f ∈ F, Measurable f) (hpm : IsPointwiseMeasurableClass F)
    {k : ℝ} (hk : ∀ (m : ℕ) (z : Fin m → X), Shatters F z → (m : ℝ) ≤ k)
    (D : Measure X) [IsProbabilityMeasure D] {U : ℝ}
    (hU : ∀ᵐ v ∂D, ∀ f ∈ F, f v ∈ Set.Icc 0 U)
    {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Measure.pi (fun _ : Fin N => D)
      {S : Fin N → X | ∃ f ∈ F,
        120 * U * √(k / (N : ℝ)) + 4 * U * √(2 * Real.log (4 / δ) / (N : ℝ)) <
          |(1 / (N : ℝ)) * ∑ i, f (S i) - ∫ v, f v ∂D|} < ENNReal.ofReal δ := by sorry

end SampleMechDesign
