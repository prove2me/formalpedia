-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_theorem_A_2
-- name    : SingleSampleCombPI.XOS.Supplement.theorem_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:53:08.580452+00:00
-- url     : https://prove2.me/theorems/7f732528-5054-4418-8815-db00c04315ac
-- title:
--   Theorem A.2 — Arbitrary-alpha exact harmonic transfer to subadditive buyers
-- statement:
--   Let $m\ge1$ and $\alpha\in[0,1]$. Given any family of $\alpha$-competitive feasible single-sample XOS allocation policies over $m$ indivisible items, there is one deterministic valuation map $T$ supplying XOS approximations
--   $$v(S)/H_m\le T(v)(S)\le v(S)$$
--   for every normalized monotone subadditive $v$ and every bundle $S$. Applying this same map to samples and real arrivals yields feasible policies with exact guarantee $\alpha/H_m$ for every buyer count and every fixed arrival order in GoG. The quantitative logarithmic consequence is $\alpha/(2\log m)\le\alpha/H_m$ for $m\ge3$. No efficiency or approximation-oracle input assumption is made.
--
--   Differences from the source:
--   - encoding: XOS and subadditive online allocation with valuation access → native bundle policies with revealed-prefix access, finite feasible benchmarks and fair GoG averaging; reason: subadditive inputs carry no supporting-price or demand oracle; finite bundle maxima are exactly the source optima
--   - generalization: existence of a transferred policy → existence of the deterministic XOS sandwich map used in the proof together with its transferred policies; reason: the additional map conclusion is the source proof construction and implies the whole source transfer
--   - encoding: Ω(α/log m) → the explicit comparison α/(2 log m)≤α/H_m for m≥3; reason: H_m≤1+log m≤2 log m in this range; the exact harmonic factor is retained and the excluded small m are still covered by it
--   - encoding: expectations over the specified independent random choices → explicit fair finite GoG averages and nonnegative expectations over independent algorithm seeds; reason: these are ordinary expectations for measurable source payoffs; no input distribution or finite-support restriction is imposed
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Theorem A.2, printed p. 36 / PDF p. 38; proof printed 36 / PDF 38.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Transfer

namespace SingleSampleCombPI.XOS.Supplement

/-- Theorem A.2, PDF 38 / printed 36. The approximation is a conclusion, not
an extra hypothesis or input oracle. Every admissible alpha is transferred. -/
theorem theorem_A_2 (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : α ∈ Set.Icc 0 1)
    (S : (n : ℕ) → BundlePolicy n m)
    (hS : ∀ n, (S n).Guarantee BundleXOS α) :
    ∃ T : BundleValue m → BundleValue m,
      (∀ v, BundleSubadditive v → BundleXOS (T v) ∧
        ∀ U, v U / harmonic m ≤ T v U ∧ T v U ≤ v U) ∧
      (∀ n, (transformPolicy T (S n)).Guarantee BundleSubadditive (α/harmonic m)) ∧
      (3 ≤ m → α/(2*Real.log m) ≤ α/harmonic m) := by sorry

end SingleSampleCombPI.XOS.Supplement
