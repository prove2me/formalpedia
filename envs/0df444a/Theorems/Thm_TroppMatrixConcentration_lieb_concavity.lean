-- Prove2me | Theorems.Thm_TroppMatrixConcentration_lieb_concavity
-- name    : TroppMatrixConcentration.lieb_concavity
-- status  : Proved
-- author  : @tc
-- created : 2026-10-07T13:53:58.56744+00:00
-- url     : https://prove2.me/theorems/ad4e65de-12a9-48fa-9973-06de538a5ca8
-- title:
--   Theorem 8.1.1 — Lieb concavity
-- statement:
--   Fix a Hermitian complex $d\times d$ matrix $H$, with $d\ge1$. The real-valued function
--   $$A\longmapsto\operatorname{tr}\exp(H+\log A)$$
--   is concave on the convex cone of positive-definite complex $d\times d$ matrices, viewed as a real convex set. The logarithm is the spectral matrix logarithm. This concavity result is a reusable matrix-analysis input to the concentration theory.
-- source:
--   Joel A. Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1 (7 January 2015); https://arxiv.org/abs/1501.01571v1; Theorems 3.4.1 and 8.1.1, printed pp. 35 and 119; proof development Chapter 8.

import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_TroppMatrixConcentration_dilation
import Mathlib.Analysis.Convex.Function

open MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace TroppMatrixConcentration

theorem lieb_concavity {d : ℕ} [NeZero d]
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian) :
    ConcaveOn ℝ {A : Matrix (Fin d) (Fin d) ℂ | A.PosDef}
      (fun A => traceExp (H + matrixLog A)) := by sorry

end TroppMatrixConcentration
