-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P20_denjoyCarleman_zeroSet_results
-- name    : QAlgorithms.Papers.Independent.Dependency50.P20.denjoyCarleman_zeroSet_results
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:15:52.317987+00:00
-- url     : https://prove2.me/theorems/d9c21716-2481-4e1c-8c6e-b66b501a8465
-- title:
--   The printed Denjoy–Carleman growth class satisfies the zero-set conclusions
-- statement:
--   Let $d\ge 1$ be an integer and let $U\subseteq\mathbb R^d$ be a nonempty connected open set, with the Euclidean metric. For a real-valued function $f$ on $U$, write $F_U(f)=\{x\in U:f(x)=0\}$ and $G_U(f)=\{x\in U:f(x)=0,\ \|\nabla f(x)\|\ne0\}$. Lebesgue measure is understood as outer measure, so no measurability premise is needed.
--
--   For $t\in\mathbb N^d$, where $\mathbb N=\{0,1,2,\ldots\}$, write $|t|=\sum_{j=1}^d t_j$ and $D^t=\partial_1^{t_1}\cdots\partial_d^{t_d}$, without factorial normalization; $D^0f=f$.
--
--   Let $M:\mathbb N\to(0,\infty)$ satisfy $M(0)=1$, be nondecreasing with $M(n)\to+\infty$, and obey discrete log convexity $M(n+1)^2\le M(n)M(n+2)$ for every $n\ge0$. Suppose also that the positive series $\sum_{n=1}^{\infty}M(n)/M(n+1)$ diverges to $+\infty$, meaning that its partial sums tend to $+\infty$. Define $C_M(U)$ to be the smooth real-valued functions $f$ on $U$ such that, for every compact $K\subseteq U$, there are constants $C_K,R_K>0$ for which, simultaneously for every $t\in\mathbb N^d$ and $x\in K$,
--
--   $$|D^t f(x)|\le C_K R_K^{|t|}M(|t|).$$
--
--   With $\mathcal C=C_M(U)$, the conclusions are
--
--   $$\begin{gathered}\forall B\in\mathcal C,\quad\operatorname{mes}_d G_U(B)=0,\\ \forall A\in\mathcal C\text{ with }\exists x_0\in U:\ A(x_0)\ne0,\quad \operatorname{mes}_d F_U(A)=0,\qquad F_U(A)\subseteq\bigcup_{t\in\mathbb N^d}G_U(D^t A).\end{gathered}$$
--
--   This is the explicit example in the printed extension. The constants are uniform over points and derivative orders on each fixed compact set. Quasianalyticity is not an extra premise, and no factorial multiplies the displayed growth bound.
-- source:
--   The Zero Set of a Real Analytic Function, arXiv:1512.07276v1, PDF p. 3, Remark (iii), explicit C_M(U) example

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P20

open Set MeasureTheory Filter

open scoped BigOperators Topology ContDiff

namespace QAlgorithms.Papers.Independent.Dependency50.P20

/-- Remark (iii), explicit C_M(U) example, PDF p. 3: the weight and compact
uniform growth assumptions alone imply the Proposition 0 and Claims 1–2
conclusions. Quasianalyticity, nullity, and the derivative cover are not premises.
The partial sums in the weight predicate start with M(1)/M(2). -/
theorem denjoyCarleman_zeroSet_results
    {d : ℕ} (hd : 0 < d) (U : Set (Ambient d))
    (hU_open : IsOpen U) (hU_connected : IsConnected U)
    (M : ℕ → ℝ) (hM : denjoyCarlemanWeight M) :
    (∀ B : Ambient d → ℝ, inDenjoyCarlemanClass M U B →
      volume (regularZeroSet U B) = 0) ∧
    (∀ A : Ambient d → ℝ, inDenjoyCarlemanClass M U A →
      (∃ x ∈ U, A x ≠ 0) →
      volume (zeroSet U A) = 0 ∧
      zeroSet U A ⊆ ⋃ t : Fin d → ℕ, regularZeroSet U (mixedPartial t A)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P20
