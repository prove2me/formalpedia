-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_deterministic_convex
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.deterministic_convex
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:37:23.019084+00:00
-- url     : https://prove2.me/theorems/cb729941-d6cd-4592-80aa-e3eccdfcfd6d
-- title:
--   §IV A: convex geometry of deterministic combs
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. For a fixed ordered $N$-pair signature, $N\ge1$, let $K_N$ be the set of operationally deterministic combs. Let $A_N$ be the affine set defined by the entire recursive trace normalization, without positivity. Then
--
--   $$
--   K_N\text{ is convex over }\mathbb R,\qquad K_N=\{R:R\succeq0\}\cap A_N.
--   $$
--
--   The affine constraints retain all prefixes, not merely the final partial trace.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 12, §IV A: convex geometry of deterministic combs

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.12, convex geometry paragraph: retain both convexity and the affine-cone intersection. -/
theorem deterministic_convex (s : Signature) (n : ℕ) (hn : 0 < n) :
    Convex ℝ {R : Matrix (Basis s n) (Basis s n) ℂ | Deterministic n s R} ∧
      {R : Matrix (Basis s n) (Basis s n) ℂ | Deterministic n s R} =
      {R | R.PosSemidef ∧ AffineNormalized s n R} := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
