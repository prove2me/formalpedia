-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_neighpl_mul
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.neighpl_mul
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:51:50.429985+00:00
-- url     : https://prove2.me/theorems/ec759708-ebd2-458b-9be7-765577b9735b
-- title:
--   §4.2, Lemma neighpl_mul
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. Let $N_-(P,a,b)=(v(P,a,b),b)$, where $v$ is the preceding-root function with the source's dual defaults. Then
--
--   $$\forall x,\quad x\in N_-(PQ,a,b)\iff x\in N_-(P,a,b)\land x\in N_-(Q,a,b).$$
--
--   This is pointwise equality of membership predicates, including degenerate neighborhoods.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 20, §4.2, Lemma neighpl_mul

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 20, neighpl_mul, as pointwise membership equality. -/
theorem neighpl_mul {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (a b : R) (p q : Polynomial R) :
    ∀ x, x ∈ neighpl (p * q) a b ↔ x ∈ neighpl p a b ∧ x ∈ neighpl q a b := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
