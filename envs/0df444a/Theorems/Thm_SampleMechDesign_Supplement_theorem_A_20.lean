-- Prove2me | Theorems.Thm_SampleMechDesign_Supplement_theorem_A_20
-- name    : SampleMechDesign.Supplement.theorem_A_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T22:54:15.602232+00:00
-- url     : https://prove2.me/theorems/e9ae3a6c-f87b-584d-ae5b-e99ed131a61e
-- title:
--   Theorem A.20 (corrected: the auction $M^*$ is chosen after the sample) — λ-auctions overfit samples of size at most $(n^m-n)/2$
-- statement:
--   For any $n$, $m$ and any $\epsilon\in(0,1)$ there is a finitely supported distribution $\mathcal D$ over additive valuation vectors such that, for every sample size $N$ with $1\le N\le(n^m-n)/2$, with probability $1$ over $S\sim\mathcal D^N$ there is a λ-auction $M^*$ with
--   $$
--   \frac1{|S|}\sum_{v\in S}\mathrm{profit}_{M^*}(v)-\mathop{\mathbb E}_{v\sim\mathcal D}\big[\mathrm{profit}_{M^*}(v)\big]\ >\ \epsilon .
--   $$
--   The paper fixes $M^*$ before the sample, and that order is false: for $N=1$, $\mathrm{profit}_{M^*}(v)-\mathbb E_{\mathcal D}[\mathrm{profit}_{M^*}]>\epsilon$ would have to hold for $\mathcal D$-almost every $v$, which fails where the profit of $M^*$ is smallest. The proof chooses $M^*$ after $S$ (the auction $M_H$ of Theorem A.17 with $H$ the sampled points), and that is the order stated here. The cost is zero and the statement holds for every tie-breaking rule.
--
--   Differences from the source:
--   - correction: ∃ D ∃ M*, with probability 1 over S of size at most (n^m − n)/2, profit_S(M*) − profit_D(M*) > ϵ → ∃ D, for every N with 1 ≤ N ≤ (n^m − n)/2, almost surely over S ∼ D^N, ∃ λ-auction M* with profit_S(M*) − profit_D(M*) > ϵ; reason: false with M* fixed before the sample: at N = 1 it would need profit_{M*}(v) > E_D[profit_{M*}] + ϵ for D-almost every v, impossible where profit_{M*} is minimal; the proof picks M* = M_H after seeing S
--   - encoding: samples of size at most (n^m − n)/2 → 1 ≤ N ≤ (n^m − n)/2; reason: the average (1/|S|) Σ is undefined for the empty sample
--   - reading: the cost function and the tie-breaking rule is not specified → zero cost; every tie-breaking rule; reason: the construction uses zero cost; ties are left open by the paper
--   - encoding: a distribution D → a finitely supported probability measure D; reason: the proof's D is uniform on a finite set; finite support keeps every expectation a finite weighted sum
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Theorem A.20, p.36 (PDF p.36); Theorem A.17, p.34

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_amaProfit

open MeasureTheory

namespace SampleMechDesign.Supplement

/-- **Theorem A.20, quantifier order corrected.** Balcan, Sandholm, Vitercik,
arXiv:1705.00243v6, p.36. For any `n`, `m` and any `ε ∈ (0, 1)` there is a (finitely supported)
distribution `D` over additive valuation vectors such that, for every sample size `N` with
`1 ≤ N ≤ (n^m − n)/2`, with probability `1` over `S ∼ D^N` there is a λ-auction `M*` with

`(1/|S|) ∑_{v ∈ S} profit_{M*}(v) − E_{v∼D}[profit_{M*}(v)] > ε`.

**Formalization Note.**
* Correction: the paper fixes `M*` before the sample, and that is false: for `N = 1`,
  `profit_{M*}(v) − E_D[profit_{M*}] > ε` cannot hold for `D`-almost every `v` (it fails for the
  `v` of least profit in the support of `D`, or on a set of positive measure). The proof chooses
  `M*` after `S` (the `M_H` of Theorem A.17 with `H` the sampled points), and that is the order
  stated here.
* `N ≥ 1` excludes the empty sample, for which the paper's average `(1/|S|) ∑` is undefined.
  For `n ≤ 1` or `m ≤ 1` there is no admissible `N` (`n^m − n ≤ 0`), so the statement is
  trivially true there; no restriction on `n`, `m` is imposed. Zero cost, as in the construction.
* `D` is finitely supported, so every expectation is a finite weighted sum (no integrability
  junk). The statement holds for every tie-breaking rule `tb`. -/
theorem theorem_A_20 {n m : ℕ}
    (tb : BVal n m → Finset (Alloc n m) → Alloc n m) (htb : IsChoice tb) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ D : ProbabilityMeasure (AVal n m), (∃ s : Finset (AVal n m), (D : Measure (AVal n m)) (↑s)ᶜ = 0) ∧
      ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ ((n : ℝ) ^ m - n) / 2 →
        ∀ᵐ S ∂(Measure.pi fun _ : Fin N => (D : Measure (AVal n m))),
          ∃ lam : Alloc n m → ℝ, (∀ Q, 0 ≤ lam Q) ∧
            ε < (1 / (N : ℝ)) * ∑ i, amaProfit (fun _ => 0) tb (fun _ => 1) lam (additiveVal (S i)) -
              ∫ v, amaProfit (fun _ => 0) tb (fun _ => 1) lam (additiveVal v) ∂(D : Measure (AVal n m)) := by sorry

end SampleMechDesign.Supplement
