-- Prove2me | Theorems.Thm_RealAnalytic_taylor_remainder_bound
-- name    : RealAnalytic.taylor_remainder_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T19:44:04.347458+00:00
-- url     : https://prove2.me/theorems/12c3c2eb-2160-4cf8-8c8b-0fca99c6d16f
-- title:
--   Multilinear Taylor remainder estimate on a real normed-space ball
-- statement:
--   Let E be a real normed space and F a real Banach space. Suppose f:E→F is smooth on B_r(x), where r>0. Fix a displacement h with norm less than r, an integer k≥1, and M≥0. If the operator norm of the kth Frechet derivative is bounded by M everywhere on that ball, then
--
--   $$\left\| f(x+h)-\sum_{j=0}^{k-1}\frac{D^j f(x)[h,\ldots,h]}{j!}\right\|\le\frac{M}{k!}\|h\|^k.$$
--
--   The zeroth multilinear differential evaluates to f(x). The intended proof restricts f to the segment t↦x+th and applies the vector-valued one-dimensional Taylor remainder estimate. The segment lies in the ball, and each kth directional differential is bounded by M times the kth power of the norm of h. This is a finite Taylor estimate for arbitrary Banach-valued smooth functions; neither a power series nor analyticity is assumed. Its proof remains an independent obligation.
-- source:
--   Hunter, Notes on PDEs (revised 6/18/2014), Theorem 1.27 (printed p.10) and Theorem 2.10, equation (2.7) (printed p.24), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. Generalized norm form of the finite Taylor remainder, for real normed domains and Banach codomains. Mathlib.Analysis.Calculus.Taylor.exists_taylor_mean_remainder_bound supplies the one-dimensional vector-valued counterpart; this multivariate specialization is not claimed as a verbatim source statement.

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Data.Nat.Factorial.Basic

open scoped ContDiff
set_option autoImplicit false

theorem RealAnalytic.taylor_remainder_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {x h : E} {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball x r))
    (hh : ‖h‖ < r) {k : ℕ} (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ y ∈ Metric.ball x r, ‖iteratedFDeriv ℝ k f y‖ ≤ M) :
    ‖f (x + h) - ∑ j ∈ Finset.range k,
      ((j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j f x) (fun _ => h)‖ ≤
      M / (k.factorial : ℝ) * ‖h‖ ^ k := by sorry
