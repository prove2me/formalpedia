-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_diagonal_convexity
-- name    : QAlgorithms.Papers.Independent.Information100.P56.diagonal_convexity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:29:21.444302+00:00
-- url     : https://prove2.me/theorems/02d94195-4ea9-44f6-94ff-4c7ead371e44
-- title:
--   Lemma VIII.3: sufficient convexity criterion
-- statement:
--   Use $p,a,u,k,r$ and $\Delta$ as in the preceding second-derivative formula, with $0<p<1/2$. If $k\operatorname{atanh}a\ge a^3$ and $k^2\ge u^3$, then
--
--   $$\Delta''(z)\ge0\quad(|z|<1),\qquad\Delta\text{ is convex on }[-1,1].$$
--
--   Through $z=1-2x$, this also gives convexity of the original prior function on $[0,1]$. This is a sufficient criterion, with its inequalities supplied as hypotheses only in this lemma.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 23, Lemma VIII.3: sufficient convexity criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Lemma VIII.3, pp.23–24: sufficient convexity criterion, including nonnegative
second derivative on the whole open interval and convexity on the closed interval. -/
theorem diagonal_convexity (p : ℝ) (hp : 0 < p ∧ p < 1 / 2)
    (hfirst : (1 - (1 - 2 * p) ^ 2) * inverseTanh (1 - 2 * p) ≥ (1 - 2 * p) ^ 3)
    (hsecond : (1 - (1 - 2 * p) ^ 2) ^ 2 ≥ ((1 - 2 * p) ^ 2) ^ 3) :
    (∀ z : ℝ, |z| < 1 → 0 ≤ deriv (deriv (diagonalDelta p)) z) ∧
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (diagonalDelta p) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
