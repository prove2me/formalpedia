-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P20_analytic_zeroSet_hausdorffDimension
-- name    : QAlgorithms.Papers.Independent.Dependency50.P20.analytic_zeroSet_hausdorffDimension
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:14:44.392829+00:00
-- url     : https://prove2.me/theorems/2800c9ce-3d0d-403d-b47c-0bf4db1559e2
-- title:
--   The Hausdorff dimension of an analytic zero set is at most d minus one
-- statement:
--   Let $d\ge 1$ be an integer and let $U\subseteq\mathbb R^d$ be a nonempty connected open set, with the Euclidean metric. For a real-valued function $f$ on $U$, write $F_U(f)=\{x\in U:f(x)=0\}$ and $G_U(f)=\{x\in U:f(x)=0,\ \|\nabla f(x)\|\ne0\}$. Lebesgue measure is understood as outer measure, so no measurability premise is needed.
--
--   Let $A:U\to\mathbb R$ be real analytic, with $A(x_0)\ne0$ at some $x_0\in U$. Its whole zero set has Euclidean Hausdorff dimension bounded by
--
--   $$\dim_{\mathrm H}F_U(A)\le d-1.$$
--
--   This is the separate dimension assertion in Remark (ii). The extended nonnegative Hausdorff dimension convention assigns dimension zero to the empty set.
-- source:
--   The Zero Set of a Real Analytic Function, arXiv:1512.07276v1, PDF p. 3, Remark (ii), Proposition 3

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P20

open Set MeasureTheory Filter

open scoped BigOperators Topology ContDiff

namespace QAlgorithms.Papers.Independent.Dependency50.P20

/-- Proposition 3, Remark (ii), PDF p. 3: the Hausdorff dimension of the whole
zero set is at most d - 1. The explicit hypothesis d > 0 makes natural-number
subtraction agree with the source's dimension bound. -/
theorem analytic_zeroSet_hausdorffDimension
    {d : ℕ} (hd : 0 < d) (U : Set (Ambient d))
    (hU_open : IsOpen U) (hU_connected : IsConnected U)
    (A : Ambient d → ℝ) (hA : AnalyticOnNhd ℝ A U)
    (hA_nonzero : ∃ x ∈ U, A x ≠ 0) :
    dimH (zeroSet U A) ≤ (↑(d - 1) : ENNReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P20
