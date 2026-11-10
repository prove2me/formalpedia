-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_C_2
-- name    : PrivateAgnosticHalfspace.Gaussian.lemma_C_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:24:46.69114+00:00
-- url     : https://prove2.me/theorems/311941c8-0052-432d-a595-210c6fc9cf35
-- title:
--   Lemma C.2 — Hermite feature norm tail
-- statement:
--   Let $d,p\ge1$ be integers, $D_p=\binom{d+p}{p}$ and $\psi_p(x)$ the vector containing every degree-at-most-$p$ normalized Hermite polynomial once. For every $\alpha\in(0,1)$ with $d\ge2p^2/\alpha$ and $X\sim N(0,I_d)$,
--   $$
--   \Pr\bigl[\|\psi_p(X)\|_2>2\sqrt{D_p}\bigr]\le\alpha.
--   $$
--   The event is a strict upper tail, and the factor two is unchanged.
--
--   This is the dimension-dependent clipping-probability bound used by the Gaussian learner.
--
--   Differences from the source:
--   - encoding: an enumeration of all cutoff Hermites → the finite multi-index subtype with no duplicates and its Euclidean feature vector; reason: changes only coordinate representation; the exact binomial dimension and strict tail are retained
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, STOC 2027 submission #1006 (October 2026), p. 24–25, Lemma C.2; canonical PDF sha256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false

namespace PrivateAgnosticHalfspace.Gaussian

theorem lemma_C_2 (d p : ℕ) (hd : 1 ≤ d) (hp : 1 ≤ p)
    (α : ℝ) (hα : 0 < α ∧ α < 1) (hdim : (d : ℝ) ≥ 2 * (p : ℝ) ^ 2 / α) :
    (gaussian d).real {x | ‖features d p x‖ > 2 * Real.sqrt (featureDimension d p)} ≤ α := by sorry

end PrivateAgnosticHalfspace.Gaussian
