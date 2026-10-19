-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_sorted_roots
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.sorted_roots
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:47:58.801603+00:00
-- url     : https://prove2.me/theorems/325ab572-76fe-4496-a242-5ba86600e721
-- title:
--   §4.2, Lemma sorted_roots
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For every polynomial $P$ and endpoints $a,b$, the isolation list satisfies
--
--   $$\operatorname{roots}(P,a,b)\text{ is strictly increasing}. $$
--
--   Thus multiple roots appear once, and the zero-polynomial and reversed-interval conventions remain valid.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 19, §4.2, Lemma sorted_roots

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 19, sorted_roots; strict order excludes multiplicity repeats. -/
theorem sorted_roots {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (a b : R) (p : Polynomial R) :
    (roots p a b).Pairwise (· < ·) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
