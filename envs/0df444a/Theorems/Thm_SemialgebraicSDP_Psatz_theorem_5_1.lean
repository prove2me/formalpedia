-- Prove2me | Theorems.Thm_SemialgebraicSDP_Psatz_theorem_5_1
-- name    : SemialgebraicSDP.Psatz.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:03.271894+00:00
-- url     : https://prove2.me/theorems/f0bb1b88-7808-4808-944f-d84d66519b38
-- title:
--   Theorem 5.1 — (4.4) is empty iff its degree-$d$ Positivstellensatz SDP is feasible for all large $d$
-- statement:
--   Consider a system of polynomial equations and inequalities of the form (4.4), given by finite families $f_1,\dots,f_s$ (inequalities $f_j\ge0$), $g_1,\dots,g_t$ (inequations $g_k\ne0$) and $h_1,\dots,h_u$ (equations $h_\ell=0$) in $\mathbb R[x_1,\dots,x_n]$; any of $n,s,t,u$ may be $0$. For each degree level $d\in\mathbb N$, let $\mathrm{SDP}_d$ be the degree-$d$ Positivstellensatz semidefinite program: find positive semidefinite Gram matrices $Q_T$ ($T\subseteq\{1,\dots,s\}$) over the monomials of degree at most $N(d)=d(2G+1)$, $G=\sum_k\deg g_k$, and polynomials $q_\ell$ of degree at most $2N(d)$ with
--   $$
--   \sum_{T}(z^TQ_Tz)\prod_{j\in T}f_j+\Big(\prod_{k=1}^t g_k^{2d}\Big)^2+\sum_{\ell=1}^u q_\ell h_\ell=0 .
--   $$
--   Then:
--
--   1. for every $d$, if $\mathrm{SDP}_d$ is feasible, the set (4.4) is empty (a feasible point is a Positivstellensatz refutation);
--   2. if the set (4.4) is empty, there is $d_0$ such that $\mathrm{SDP}_d$ is feasible for every $d\ge d_0$.
--
--   Thus the search for bounded-degree Positivstellensatz refutations is a hierarchy of semidefinite feasibility problems that is sound at every level and complete once the degree bound is large enough.
--
--   **Formalization Note** Theorem 5.1 is a meta-statement ("the search … can be done using semidefinite programming. If the degree bound is chosen to be large enough, then the SDPs will be feasible, and the certificates obtained from its solution"). This item states it in the reading its proof fixes: "can be done using semidefinite programming" is carried by the definition of $\mathrm{SDP}_d$, a finite system of PSD constraints and linear equations; "large enough" is $\exists d_0\,\forall d\ge d_0$; "certificates obtained from its solution" is soundness at every level. The degree parameterization ($m=d$, multiplier degree $d_2=2d(2G+1)$) is a choice within the freedom the proof leaves, and meets its printed bounds $d_2\ge d$ and $d_2\ge\deg g$.
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 306, Theorem 5.1 and its proof (pp. 306–307)

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Cone
import Definitions.Def_SemialgebraicSDP_Psatz_SDP

namespace SemialgebraicSDP.Psatz

open MvPolynomial

theorem theorem_5_1 {n s t u : ℕ} (f : Fin s → MvPolynomial (Fin n) ℝ)
    (g : Fin t → MvPolynomial (Fin n) ℝ) (h : Fin u → MvPolynomial (Fin n) ℝ) :
    (∀ d : ℕ, PsatzSDPFeasible f g h d → psatzSet f g h = ∅) ∧
      (psatzSet f g h = ∅ → ∃ d₀ : ℕ, ∀ d ≥ d₀, PsatzSDPFeasible f g h d) := by sorry

end SemialgebraicSDP.Psatz
