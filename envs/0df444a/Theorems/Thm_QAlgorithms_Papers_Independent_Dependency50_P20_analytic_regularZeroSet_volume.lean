-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P20_analytic_regularZeroSet_volume
-- name    : QAlgorithms.Papers.Independent.Dependency50.P20.analytic_regularZeroSet_volume
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:13:52.268985+00:00
-- url     : https://prove2.me/theorems/22fd9848-4512-4c9e-a494-d18e2030792d
-- title:
--   The regular zero set of an analytic function is Lebesgue null
-- statement:
--   Let $d\ge 1$ be an integer and let $U\subseteq\mathbb R^d$ be a nonempty connected open set, with the Euclidean metric. For a real-valued function $f$ on $U$, write $F_U(f)=\{x\in U:f(x)=0\}$ and $G_U(f)=\{x\in U:f(x)=0,\ \|\nabla f(x)\|\ne0\}$. Lebesgue measure is understood as outer measure, so no measurability premise is needed.
--
--   For every real-analytic function $B:U\to\mathbb R$,
--
--   $$\operatorname{mes}_d G_U(B)=0.$$
--
--   This isolates the regular-zero-set result used by the paper. There is no assumption that $B$ is nontrivial; when $B=0$, its regular zero set is empty.
-- source:
--   The Zero Set of a Real Analytic Function, arXiv:1512.07276v1, PDF p. 1, Claim 1; equation (2)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P20

open Set MeasureTheory Filter

open scoped BigOperators Topology ContDiff

namespace QAlgorithms.Papers.Independent.Dependency50.P20

/-- Claim 1, PDF pp. 1–2: the regular zero set of any real-analytic B is
Lebesgue null. No nontriviality assumption is imposed on B. The reference to
F(A) in the proof on p. 2 is read as F(B), the local variable of this claim. -/
theorem analytic_regularZeroSet_volume
    {d : ℕ} (hd : 0 < d) (U : Set (Ambient d))
    (hU_open : IsOpen U) (hU_connected : IsConnected U)
    (B : Ambient d → ℝ) (hB : AnalyticOnNhd ℝ B U) :
    volume (regularZeroSet U B) = 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P20
