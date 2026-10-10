-- Prove2me | Theorems.Thm_RealAnalytic_norm_iteratedFDeriv_le_of_multiDeriv_bound
-- name    : RealAnalytic.norm_iteratedFDeriv_le_of_multiDeriv_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T19:45:49.277734+00:00
-- url     : https://prove2.me/theorems/b3f3230d-7449-4599-9e4f-2610ef5ac4d2
-- title:
--   Coordinate derivative bounds control the iterated Frechet derivative norm
-- statement:
--   Let u be a smooth real-valued function on an open subset of Euclidean n-space, and let y lie in that subset. Fix an integer k ≥ 1 and M ≥ 0. If every multi-index partial derivative of total order k has absolute value at most M at y, then
--
--   $$\|D^k u(y)\|\le (n+1)^k M.$$
--
--   The norm on the left is the operator norm of the continuous k-multilinear Frechet derivative. The partial derivatives use the fixed coordinate order of the published Hunter definition. Smoothness permits permutation of the derivative directions. Expanding each argument in the standard basis and bounding the sum of absolute coordinates by (n+1) times its Euclidean norm gives the estimate. The factor n+1 is a harmless relaxation of the usual n bound and includes dimension zero. This is a finite-order norm comparison, with no analyticity conclusion. Its proof remains an independent obligation.
-- source:
--   Hunter, Notes on PDEs (revised 6/18/2014), Section 1.8 (printed p.10), Theorem 1.27 (printed p.10), and Theorem 2.10 proof (printed pp.24–25), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. Auxiliary norm comparison extracted from the coordinate expansion of the Taylor differential; (n+1)^k relaxes the n^k coordinate bound. Not a verbatim numbered theorem.

import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

open scoped ContDiff
set_option autoImplicit false

theorem RealAnalytic.norm_iteratedFDeriv_le_of_multiDeriv_bound {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ s) {k : ℕ} (hk : 1 ≤ k)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ α : Fin n → ℕ, ∑ i, α i = k →
      |HunterPDE.Shared.multiDeriv u α y| ≤ M) :
    ‖iteratedFDeriv ℝ k u y‖ ≤ (n + 1 : ℝ) ^ k * M := by sorry
