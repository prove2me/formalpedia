-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P20_analytic_zeroSet_volume
-- name    : QAlgorithms.Papers.Independent.Dependency50.P20.analytic_zeroSet_volume
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:13:16.981966+00:00
-- url     : https://prove2.me/theorems/bb2e8fe1-ad71-4348-a3ff-9807abcf7f6f
-- title:
--   A nontrivial real-analytic function has a Lebesgue-null zero set
-- statement:
--   Let $d\ge 1$ be an integer and let $U\subseteq\mathbb R^d$ be a nonempty connected open set, with the Euclidean metric. For a real-valued function $f$ on $U$, write $F_U(f)=\{x\in U:f(x)=0\}$ and $G_U(f)=\{x\in U:f(x)=0,\ \|\nabla f(x)\|\ne0\}$. Lebesgue measure is understood as outer measure, so no measurability premise is needed.
--
--   Let $A:U\to\mathbb R$ be real analytic and suppose that $A(x_0)\ne0$ for some $x_0\in U$. Then the entire zero set satisfies
--
--   $$\operatorname{mes}_d F_U(A)=0.$$
--
--   This is the paper’s principal zero-set nullity theorem; it includes singular zeros as well as regular zeros.
-- source:
--   The Zero Set of a Real Analytic Function, arXiv:1512.07276v1, PDF p. 1, Proposition 0

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P20

open Set MeasureTheory Filter

open scoped BigOperators Topology ContDiff

namespace QAlgorithms.Papers.Independent.Dependency50.P20

/-- Proposition 0, PDF p. 1 (proof completed on p. 3): the whole zero set of a
nontrivial real-analytic function on a connected open domain is Lebesgue null.
The nonzero witness lies in U. Volume here also expresses outer nullity. -/
theorem analytic_zeroSet_volume
    {d : ℕ} (hd : 0 < d) (U : Set (Ambient d))
    (hU_open : IsOpen U) (hU_connected : IsConnected U)
    (A : Ambient d → ℝ) (hA : AnalyticOnNhd ℝ A U)
    (hA_nonzero : ∃ x ∈ U, A x ≠ 0) :
    volume (zeroSet U A) = 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P20
