-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_strict_witness
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.strict_witness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:58:26.338436+00:00
-- url     : https://prove2.me/theorems/72d3c140-fecd-4fbf-8e36-496988c54322
-- title:
--   §6.2.1, strict-only witness reduction
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. Let $\mathcal Q$ be a finite polynomial list. If some $x\in R$ makes all its polynomials strictly positive, then there is $y\in R$ such that all remain strictly positive and
--
--   $$[\forall Q\in\mathcal Q,\forall r,\ Q(r)=0\Rightarrow r<y]\ \lor\ [\forall Q\in\mathcal Q,\forall r,\ Q(r)=0\Rightarrow y<r]\ \lor\ \left(\prod_{Q\in\mathcal Q}Q\right)'(y)=0.$$
--
--   The first two alternatives are ordinary field witnesses past all roots, rather than infinite values. The empty-list case is included.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 31, §6.2.1, strict-only witness reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 31, strict-only witness reduction. Infinity means an ordinary
field point strictly past all roots. Positivity is retained in every branch. -/
theorem strict_witness {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (qs : List (Polynomial R))
    (h : ∃ x : R, ∀ q ∈ qs, 0 < q.eval x) :
    ∃ y : R, (∀ q ∈ qs, 0 < q.eval y) ∧
      ((∀ q ∈ qs, ∀ r : R, q.eval r = 0 → r < y) ∨
       (∀ q ∈ qs, ∀ r : R, q.eval r = 0 → y < r) ∨
       qs.prod.derivative.eval y = 0) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
