-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P32_homogeneous_diagonal_linearization
-- name    : QAlgorithms.Papers.Independent.Renew46.P32.homogeneous_diagonal_linearization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:16:40.193848+00:00
-- url     : https://prove2.me/theorems/ad7b1238-49aa-4f1e-a941-8170f0eeee83
-- title:
--   Diagonal polarization of a homogeneous map
-- statement:
--   Let $K$ be a commutative unital ring, $E,F$ be $K$-modules, and $q:E\to F$ satisfy $q(tx)=t^kq(x)$ for every $t\in K$ and $x\in E$, where $k\ge0$. Then
--   $$L_kq(0;x,\ldots,x)=k!\,q(x)\qquad(x\in E).$$
--
--   Here $L_k$ is the iterated forward difference and $k!$ acts by repeated addition in $F$. The identity includes degree zero and requires no division or multilinearity.
-- source:
--   Differential Calculus, Manifolds and Lie Groups over Arbitrary Infinite Fields, arXiv:math/0303300v1, PDF p. 65, Lemma A.4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P32

namespace QAlgorithms.Papers.Independent.Renew46.P32

open Set Filter Topology

universe u v

section AlgebraicDefinitions

variable {K : Type u} [CommRing K]

variable {E : Type u} [AddCommGroup E] [Module K E]

variable {F : Type u} [AddCommGroup F] [Module K F]

/-- Lemma A.4, PDF p. 65: no multilinearity, differentiability, or
invertibility of the factorial is assumed. -/
theorem homogeneous_diagonal_linearization
    (q : E → F) (k : ℕ) (hq : IsScalarHomogeneous (K := K) k q) :
    ∀ x : E, linearization q 0 k (fun _ => x) = (Nat.factorial k) • q x := by sorry

end AlgebraicDefinitions

end QAlgorithms.Papers.Independent.Renew46.P32
