-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P20_analytic_zeroSet_derivative_cover
-- name    : QAlgorithms.Papers.Independent.Dependency50.P20.analytic_zeroSet_derivative_cover
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:14:13.361426+00:00
-- url     : https://prove2.me/theorems/72b9e332-8b3e-4b44-91d4-2c3c37f04f66
-- title:
--   Analytic zeros are covered by regular zeros of mixed derivatives
-- statement:
--   Let $d\ge 1$ be an integer and let $U\subseteq\mathbb R^d$ be a nonempty connected open set, with the Euclidean metric. For a real-valued function $f$ on $U$, write $F_U(f)=\{x\in U:f(x)=0\}$ and $G_U(f)=\{x\in U:f(x)=0,\ \|\nabla f(x)\|\ne0\}$. Lebesgue measure is understood as outer measure, so no measurability premise is needed.
--
--   For $t\in\mathbb N^d$, where $\mathbb N=\{0,1,2,\ldots\}$, write $|t|=\sum_{j=1}^d t_j$ and $D^t=\partial_1^{t_1}\cdots\partial_d^{t_d}$, without factorial normalization; $D^0f=f$.
--
--   If $A:U\to\mathbb R$ is real analytic and $A(x_0)\ne0$ at some $x_0\in U$, then
--
--   $$F_U(A)\subseteq\bigcup_{t\in\mathbb N^d}G_U(D^t A).$$
--
--   The union is countable because $d$ is finite. It is the explicit derivative cover established in equation (8), and covers singular as well as regular zeros of $A$.
-- source:
--   The Zero Set of a Real Analytic Function, arXiv:1512.07276v1, PDF p. 2, Claim 2; equation (8), PDF p. 3

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P20

open Set MeasureTheory Filter

open scoped BigOperators Topology ContDiff

namespace QAlgorithms.Papers.Independent.Dependency50.P20

/-- Claim 2, PDF pp. 2–3, pinned to the explicit inclusion (8) on p. 3.
The countable indexing type is N^d and includes the zero multi-index. The
covering functions are the derivatives of A, rather than a free family. -/
theorem analytic_zeroSet_derivative_cover
    {d : ℕ} (hd : 0 < d) (U : Set (Ambient d))
    (hU_open : IsOpen U) (hU_connected : IsConnected U)
    (A : Ambient d → ℝ) (hA : AnalyticOnNhd ℝ A U)
    (hA_nonzero : ∃ x ∈ U, A x ≠ 0) :
    zeroSet U A ⊆ ⋃ t : Fin d → ℕ, regularZeroSet U (mixedPartial t A) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P20
