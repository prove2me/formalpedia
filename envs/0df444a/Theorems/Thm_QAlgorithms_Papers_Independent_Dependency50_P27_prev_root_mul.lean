-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_prev_root_mul
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.prev_root_mul
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:51:21.682486+00:00
-- url     : https://prove2.me/theorems/28e40d00-ac0d-4d7f-bc74-a920644fe925
-- title:
--   §4.2, explicitly named left counterpart prev_root_mul
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. Define $v(P,a,b)=b$ for $P=0$; otherwise use the last root in $(a,b)$, with default $\min(a,b)$ when its root list is empty. For all inputs,
--
--   $$v(PQ,a,b)=\max(v(P,a,b),v(Q,a,b)).$$
--
--   This is the explicitly named order-dual counterpart, with left neighborhood $(v(P,a,b),b)$.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 20, §4.2, explicitly named left counterpart prev_root_mul

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 20, explicitly named left counterpart prev_root_mul. -/
theorem prev_root_mul {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (a b : R) (p q : Polynomial R) :
    prevRoot (p * q) a b = max (prevRoot p a b) (prevRoot q a b) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
