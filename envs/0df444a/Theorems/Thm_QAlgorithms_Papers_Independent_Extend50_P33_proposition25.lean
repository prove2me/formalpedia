-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_proposition25
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.proposition25
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:07:49.066996+00:00
-- url     : https://prove2.me/theorems/98277e5b-e9c0-4a26-ab3e-473dd2d74a6d
-- title:
--   Proposition 25: ratio of consecutive multiplicity-square sums
-- statement:
--   Let $d\ge2$ and $r\ge1$. For the actual tensor multiplicities define $S_r=\sum_{\nu\vdash r,\,h(\nu)\le d}m_\nu^2$. The lower-degree sum is positive, and
--
--   $$\frac{S_r}{S_{r-1}}=\frac{d^2+r-1}{r}.$$
--
--   The formal parameters write the degree as a successor to exclude division by zero. Taking $r=N$ evaluates the jointly optimized success probability.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 25, Proposition 25: ratio of consecutive multiplicity-square sums

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- PDF p.25 Proposition25: denominator is positive and degree r+1≥1. -/
theorem proposition25 (d r : ℕ) (hd : 2 ≤ d) :
    0 < squareSum d r ∧
    squareSum d (r+1) / squareSum d r = ((d:ℝ)^2 + r) / (r+1:ℕ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
