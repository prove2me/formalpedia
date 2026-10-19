-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_next_root_mul
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.next_root_mul
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:50:00.109554+00:00
-- url     : https://prove2.me/theorems/e8086648-2e5d-44aa-8976-876f9e06b1d7
-- title:
--   §4.2, Lemma next_root_mul
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. Define $n(P,a,b)=a$ for $P=0$; otherwise use the first root in $(a,b)$, with default $\max(b,a)$ when its root list is empty. For all $P,Q,a,b$,
--
--   $$n(PQ,a,b)=\min(n(P,a,b),n(Q,a,b)).$$
--
--   The defaults make the identity valid even for zero factors and reversed endpoints.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 19, §4.2, Lemma next_root_mul

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF pp. 19–20, next_root_mul, including degenerate inputs. -/
theorem next_root_mul {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (a b : R) (p q : Polynomial R) :
    nextRoot (p * q) a b = min (nextRoot p a b) (nextRoot q a b) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
