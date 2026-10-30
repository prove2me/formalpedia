-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_asymptotic_success
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.asymptotic_success
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:57:45.848989+00:00
-- url     : https://prove2.me/theorems/ead4a914-6664-4e84-b27c-6dc6a374c47d
-- title:
--   Unnumbered consequence: limits and comparison of probabilistic schemes
-- statement:
--   For $d,N\ge2$, write $p(d,N)=N/(N+d^2-1)$ for the joint optimum and $p_{\rm ME}(d,N)$ for the fixed-resource optimum of Theorem 3. Then
--
--   $$\lim_{N\to\infty}p(d,N)=1\quad(d\text{ fixed}),\qquad\lim_{d\to\infty}p(d,N)=0\quad(N\text{ fixed}),\qquad p_{\rm ME}(d,N)\le p(d,N).$$
--
--   The limits are along natural dimensions and port counts; no simultaneous scaling is asserted.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 13, Unnumbered consequence: limits and comparison of probabilistic schemes

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

/-- PDF p.13 unnumbered consequence: fixed-d and fixed-N limits, and comparison
with the fixed maximally entangled resource. -/
theorem asymptotic_success :
    (∀ d : ℕ, 2 ≤ d → Filter.Tendsto (fun N : ℕ => optimalProbability d N)
      Filter.atTop (nhds 1)) ∧
    (∀ N : ℕ, 2 ≤ N → Filter.Tendsto (fun d : ℕ => optimalProbability d N)
      Filter.atTop (nhds 0)) ∧
    (∀ d k : ℕ, 2 ≤ d → fixedRatioValue d k ≤ optimalProbability d (k+2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
