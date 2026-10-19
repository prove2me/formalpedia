-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P20_quasianalytic_zeroSet_results
-- name    : QAlgorithms.Papers.Independent.Dependency50.P20.quasianalytic_zeroSet_results
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:15:24.025163+00:00
-- url     : https://prove2.me/theorems/019812d5-ce98-4343-9527-07a00b662e72
-- title:
--   Proposition 0 and Claims 1–2 extend to real quasianalytic classes
-- statement:
--   Let $d\ge 1$ be an integer and let $U\subseteq\mathbb R^d$ be a nonempty connected open set, with the Euclidean metric. For a real-valued function $f$ on $U$, write $F_U(f)=\{x\in U:f(x)=0\}$ and $G_U(f)=\{x\in U:f(x)=0,\ \|\nabla f(x)\|\ne0\}$. Lebesgue measure is understood as outer measure, so no measurability premise is needed.
--
--   For $t\in\mathbb N^d$, where $\mathbb N=\{0,1,2,\ldots\}$, write $|t|=\sum_{j=1}^d t_j$ and $D^t=\partial_1^{t_1}\cdots\partial_d^{t_d}$, without factorial normalization; $D^0f=f$.
--
--   Let $\mathcal C$ be a class of real-valued smooth functions on $U$ containing zero. Assume local Taylor-jet uniqueness: whenever $f,g\in\mathcal C$ and $x\in U$ satisfy $D^t f(x)=D^t g(x)$ for every $t\in\mathbb N^d$, there is an open neighborhood $V$ of $x$ contained in $U$ on which $f=g$.
--
--   Then all three zero-set conclusions hold:
--
--   $$\begin{gathered}\forall B\in\mathcal C,\quad\operatorname{mes}_d G_U(B)=0,\\ \forall A\in\mathcal C\text{ with }\exists x_0\in U:\ A(x_0)\ne0,\quad \operatorname{mes}_d F_U(A)=0,\qquad F_U(A)\subseteq\bigcup_{t\in\mathbb N^d}G_U(D^t A).\end{gathered}$$
--
--   This gives precisely the printed quasianalytic extension. Claim 1 remains universal, including the zero function; the extension does not assert a Hausdorff-dimension conclusion.
-- source:
--   The Zero Set of a Real Analytic Function, arXiv:1512.07276v1, PDF p. 3, Remark (iii), general assertion

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P20

open Set MeasureTheory Filter

open scoped BigOperators Topology ContDiff

namespace QAlgorithms.Papers.Independent.Dependency50.P20

/-- Remark (iii), PDF p. 3: Proposition 0 and Claims 1 and 2, including the
explicit cover (8), extend to any real quasianalytic class. Claim 1 is universal
over B, including B = 0. Only the nullity and cover clauses require A to be
nontrivial. Proposition 3 is not included in the printed extension. -/
theorem quasianalytic_zeroSet_results
    {d : ℕ} (hd : 0 < d) (U : Set (Ambient d))
    (hU_open : IsOpen U) (hU_connected : IsConnected U)
    (C : Set (Ambient d → ℝ)) (hC : isQuasianalyticClass U C) :
    (∀ B ∈ C, volume (regularZeroSet U B) = 0) ∧
    (∀ A ∈ C, (∃ x ∈ U, A x ≠ 0) →
      volume (zeroSet U A) = 0 ∧
      zeroSet U A ⊆ ⋃ t : Fin d → ℕ, regularZeroSet U (mixedPartial t A)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P20
