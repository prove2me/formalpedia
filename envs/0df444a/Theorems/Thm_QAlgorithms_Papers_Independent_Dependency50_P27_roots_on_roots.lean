-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_roots_on_roots
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.roots_on_roots
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:47:39.740136+00:00
-- url     : https://prove2.me/theorems/089bd582-330d-4638-916d-af88a6ef7448
-- title:
--   §4.2, Lemma roots_on_roots
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For $P\ne0$ and arbitrary endpoints $a,b$, the list produced by root isolation has exactly the roots in the open interval:
--
--   $$\forall x\in R,\quad x\in\operatorname{roots}(P,a,b)\iff (a<x<b\land P(x)=0).$$
--
--   Both exhaustiveness and exclusion of spurious entries are asserted.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 19, §4.2, Lemma roots_on_roots

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 19, roots_on_roots. -/
theorem roots_on_roots {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) (hp : p ≠ 0) :
    rootsOn p a b (roots p a b) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
