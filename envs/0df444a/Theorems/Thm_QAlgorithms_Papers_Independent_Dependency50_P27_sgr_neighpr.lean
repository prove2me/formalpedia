-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_sgr_neighpr
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.sgr_neighpr
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:52:36.552477+00:00
-- url     : https://prove2.me/theorems/a699f092-d808-4609-96d9-0844c168ff3a
-- title:
--   §4.2, Lemma sgr_neighpr
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For $N_+(P,x,b)=(x,n(P,x,b))$, and $s_+(P,x)$ the first nonzero formal-derivative sign including derivative order zero,
--
--   $$\forall y\in N_+(P,x,b),\quad\operatorname{sgn}(P(y))=s_+(P,x).$$
--
--   No nonzero or endpoint-order guard is needed: the corresponding degenerate neighborhoods are empty.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 20, §4.2, Lemma sgr_neighpr

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF pp. 20–21, sgr_neighpr; empty neighborhoods need no extra guard. -/
theorem sgr_neighpr {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (b : R) (p : Polynomial R) (x : R) :
    ∀ y ∈ neighpr p x b, sgr (p.eval y) = rightSign p x := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
