-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_polynomialDegree_finiteDifference_equivalences
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.polynomialDegree_finiteDifference_equivalences
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:16:18.27699+00:00
-- url     : https://prove2.me/theorems/6b739964-2364-443a-95ee-be88822123d6
-- title:
--   Finite-difference degree and separate additivity
-- statement:
--   Let $E,F$ be abelian groups, let $q:E\to F$, and let $k\ge1$ be an integer. Define $L_jq(x;v_1,\ldots,v_j)=\Delta_{v_1}\cdots\Delta_{v_j}q(x)$. The following are equivalent: $L_{k+1}q$ vanishes at every base point; $L_{k+1}q(0;\cdot)$ vanishes; $L_kq(x;\cdot)$ is additive in each of its $k$ arguments for every $x$; and $L_kq(0;\cdot)$ is additive in each argument. In particular, the vanishing condition is
--   $$L_{k+1}q(x;v_0,\ldots,v_k)=0\qquad(x,v_0,\ldots,v_k\in E).$$
--
--   This relates finite-difference degree to separate additivity in general abelian groups.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 65, Proposition A.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

section AlgebraicDefinitions

variable {K : Type u} [CommRing K]

variable {E : Type u} [AddCommGroup E] [Module K E]

variable {F : Type u} [AddCommGroup F] [Module K F]

/-- Proposition A.3, PDF p. 65: k is positive, as required by the proof's
first direction. At k=0 separate additivity would be vacuous. -/
theorem polynomialDegree_finiteDifference_equivalences
    {A : Type u} [AddCommGroup A] {B : Type u} [AddCommGroup B]
    (q : A → B) (k : ℕ) (hk : 0 < k) :
    List.TFAE [
      (∀ x : A, ∀ h : Fin (k + 1) → A, linearization q x (k + 1) h = 0),
      (∀ h : Fin (k + 1) → A, linearization q 0 (k + 1) h = 0),
      (∀ x : A, IsMultiadditive (linearization q x k)),
      IsMultiadditive (linearization q 0 k)
    ] := by sorry

end AlgebraicDefinitions

end QAlgorithms.Papers.Independent.Renew46.P32
