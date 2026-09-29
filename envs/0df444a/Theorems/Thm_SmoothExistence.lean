-- Prove2me | Theorems.Thm_SmoothExistence
-- name    : SmoothExistence
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:00:52.228508+00:00
-- url     : https://prove2.me/theorems/0b28e314-16d7-47f6-a966-b140fe3f73ee
-- title:
--   Existence of a smooth nonnegative bump $\nu$ on $[1/2, 2]$ with $\int_0^\infty \nu(x)\,dx/x = 1$
-- statement:
--   There exists a function $\nu : \mathbb{R} \to \mathbb{R}$ with all of the following properties:
--
--   $$\nu \in C^\infty(\mathbb{R}), \qquad \nu \ge 0 \text{ on all of } \mathbb{R}, \qquad \operatorname{supp}\nu \subseteq \left[\tfrac{1}{2},\, 2\right], \qquad \int_{[0,\infty)} \frac{\nu(x)}{x}\, dx = 1.$$
--
--   That is: $\nu$ is an infinitely differentiable, everywhere-nonnegative bump function, vanishing outside the interval $[1/2, 2]$, normalized to have total mass one with respect to the multiplicative Haar measure $dx/x$ on the positive reals.
--
--   This existence statement furnishes the mollifier that the entire smoothed-Chebyshev approach to the Prime Number Theorem is built on: every hypothesis of the form "let the smoothing kernel be $C^1$ (or $C^\infty$), nonnegative, supported in $[1/2,2]$, of mass one" appearing in the Mellin calculus and contour-integration lemmas is discharged by this single construction (a standard $e^{-1/x}$-type bump, rescaled and normalized). It is reusable wherever a normalized compactly supported mollifier for multiplicative convolution is needed.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/SmoothExistence.lean#L45-L91

import Batteries.Tactic.Lemma
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Bound
import Mathlib.Algebra.Notation.Support

set_option lang.lemmaCmd true

open MeasureTheory Set Real
open scoped ContDiff

theorem SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by sorry
