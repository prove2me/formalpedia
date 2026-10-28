-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_roots_exist
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.roots_exist
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:46:44.171993+00:00
-- url     : https://prove2.me/theorems/264f0469-b831-467f-ad8b-434de52ae76b
-- title:
--   §4.2, unnumbered existence of exhaustive sorted roots
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For every $P\in R[X]$ and $a,b\in R$ there exists a finite strictly increasing list $s$ such that
--
--   $$ (P=0\land s=[])\quad\lor\quad(P\ne0\land\forall x,\ x\in s\iff a<x<b\land P(x)=0).$$
--
--   The zero case is an empty-list convention, not an exhaustive enumeration of the zero polynomial's roots. For reversed endpoints the exhaustive list is empty.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 18, §4.2, unnumbered existence of exhaustive sorted roots

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 18, existence of a strictly ordered exhaustive sequence.
The empty list for zero is not asserted to enumerate every zero of zero. -/
theorem roots_exist {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) :
    ∃ s : List R, s.Pairwise (· < ·) ∧
      ((p = 0 ∧ s = []) ∨ (p ≠ 0 ∧ rootsOn p a b s)) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
