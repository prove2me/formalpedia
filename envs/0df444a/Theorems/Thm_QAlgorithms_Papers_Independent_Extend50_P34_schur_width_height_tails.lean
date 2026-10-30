-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_schur_width_height_tails
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.schur_width_height_tails
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:51:22.620399+00:00
-- url     : https://prove2.me/theorems/95e6ad9d-e524-4984-87df-028d2c0b8397
-- title:
--   Proposition 2.31
-- statement:
--   For $\lambda\sim\mathrm{SW}_d^n$, $d\ge1$, $n\ge0$, and an integer $B\ge1$, both width and height obey
--
--   $$\Pr[\lambda_1\ge B],\ \Pr[\lambda'_1\ge B]\le\left(\frac{(1+B/d)e^2n}{B^2}\right)^B.$$
--
--   This remains valid when $B>n$, where both events are empty. The bound may exceed one; it is an explicit tail bound rather than an asymptotic approximation.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 24, Proposition 2.31

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Proposition 2.31, arXiv:1501.05028v1, PDF p.24.  -/
theorem schur_width_height_tails
    (d n B : ℕ) (hd : 0 < d) (hB : 0 < B) :
    event (n := n) (unif d) (fun lambda => B ≤ lambda.rowLen 0) ≤
      (((1 + (B : ℝ)/d) * Real.exp 2 * n) / (B : ℝ)^2)^B ∧
    event (n := n) (unif d) (fun lambda => B ≤ lambda.colLen 0) ≤
      (((1 + (B : ℝ)/d) * Real.exp 2 * n) / (B : ℝ)^2)^B := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
