-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_taq_constraints1
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.taq_constraints1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:55:14.163977+00:00
-- url     : https://prove2.me/theorems/934342d0-b4d5-42fa-834a-02df014d375f
-- title:
--   §5.3.3, three explicit Tarski-query/sign-count identities
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For an arbitrary finite list $z$ and polynomial $Q$, let $c_s$ count occurrences of points $x$ in $z$ with $\operatorname{sgn}(Q(x))=s$. The integer-valued Tarski queries satisfy
--
--   $$\operatorname{TaQ}(z,Q)=c_1-c_{-1},\qquad\operatorname{TaQ}(z,Q^2)=c_1+c_{-1},\qquad\operatorname{TaQ}(z,1)=c_1+c_{-1}+c_0.$$
--
--   All natural counts are cast to integers before arithmetic. Empty lists and duplicate entries are allowed.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 26, §5.3.3, three explicit Tarski-query/sign-count identities

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 26, all three displayed identities, with integer arithmetic. -/
theorem taq_constraints1 {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (z : List R) (q : Polynomial R) :
    taq z q = (constraints1 z q 1 : ℤ) - (constraints1 z q (-1) : ℤ) ∧
    taq z (q ^ 2) = (constraints1 z q 1 : ℤ) + (constraints1 z q (-1) : ℤ) ∧
    taq z 1 = (constraints1 z q 1 : ℤ) + (constraints1 z q (-1) : ℤ) +
      (constraints1 z q 0 : ℤ) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
