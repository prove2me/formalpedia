-- Prove2me | Theorems.Thm_RealAnalytic_analyticAt_of_multiDeriv_bound
-- name    : RealAnalytic.analyticAt_of_multiDeriv_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T16:29:10.908976+00:00
-- url     : https://prove2.me/theorems/beecc48a-4f59-4ffa-b122-9f10a0627c09
-- title:
--   Local factorial bounds on partial derivatives imply real analyticity
-- statement:
--   Let $n\in\mathbb N$, let $u:\mathbb R^n\to\mathbb R$, and fix $x\in\mathbb R^n$. Suppose $r>0$, $C\ge0$, $A>0$, and $u$ is smooth on the open ball $B_r(x)$. If every partial derivative of positive order obeys the uniform bound
--
--   $$|\partial^\alpha u(y)|\le C A^k k!,\qquad y\in B_r(x),\quad |\alpha|=k\ge1,$$
--
--   then $u$ is real-analytic at $x$: it has a convergent formal multilinear power series representing it on a neighbourhood of $x$.
--
--   The hypothesis is uniform on a whole ball, not merely at its centre. The order-zero derivative requires no bound. For smooth functions, the fixed coordinate order in the imported multi-index derivative agrees with any order by symmetry of mixed derivatives. This criterion applies to arbitrary smooth functions and makes no harmonicity assumption. Dimension zero is included.
--
--   The usual proof bounds the multivariable Taylor remainder by $C(nA\|h\|)^k$ and lets $k$ tend to infinity for sufficiently small $h$. Construction of the convergent multilinear series and this remainder argument are the proof obligation of this open prerequisite.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), Theorem 2.10 proof, printed pp. 24–25, especially equations (2.7)–(2.8); https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf. Generalized analytic criterion extracted from the Taylor-remainder argument, with arbitrary factorial/geometric constants instead of harmonic estimates.

import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Nat.Factorial.Basic

open scoped ContDiff
set_option autoImplicit false

theorem RealAnalytic.analyticAt_of_multiDeriv_bound {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {r C A : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hA : 0 < A)
    (hu : ContDiffOn ℝ ∞ u (Metric.ball x r))
    (hbound : ∀ y ∈ Metric.ball x r, ∀ (α : Fin n → ℕ) (k : ℕ),
      ∑ i, α i = k → 1 ≤ k →
      |HunterPDE.Shared.multiDeriv u α y| ≤ C * A ^ k * (k.factorial : ℝ)) :
    AnalyticAt ℝ u x := by sorry
