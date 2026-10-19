-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_monic_reduction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.monic_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:53:21.485372+00:00
-- url     : https://prove2.me/theorems/e623d0db-352a-4cad-be6b-106a844a9747
-- title:
--   §5.2, unnumbered monic change of variable
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. Let $P$ have degree $d\ge1$ and leading coefficient $l$. For a finite list $\mathcal Q$ of polynomials, define
--
--   $$S(Y)=Y^d+\sum_{i<d}p_i l^{d-1-i}Y^i,\qquad T_l(Q)(Y)=\sum_{i=0}^{e}q_i l^{2e-i}Y^i,\quad e=\deg Q.$$
--
--   For $Q=0$ use $e=0$ and its zero coefficient. Then $S$ is monic, $S(lX)=l^{d-1}P(X)$, and
--
--   $$[\exists x,\ P(x)=0\land\bigwedge_{Q\in\mathcal Q}Q(x)>0]\iff[\exists y,\ S(y)=0\land\bigwedge_{Q\in\mathcal Q}T_l(Q)(y)>0].$$
--
--   The even factor preserves signs for negative $l$, and the formula also includes the linear case.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 22, §5.2, unnumbered monic change of variable

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF pp. 22–23, monic change of variable. The printed R naming S is
read as S, following the displayed identity. Zero/constant equations are excluded
from this branch, not encoded using negative truncated exponents. -/
theorem monic_reduction {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (qs : List (Polynomial R))
    (hdegree : 1 ≤ p.natDegree) :
    (monicTransform p).Monic ∧
    (monicTransform p).comp (C p.leadingCoeff * X) =
      C (p.leadingCoeff ^ (p.natDegree - 1)) * p ∧
    (feasible p qs ↔ feasible (monicTransform p) (qs.map (signTransform p.leadingCoeff))) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
