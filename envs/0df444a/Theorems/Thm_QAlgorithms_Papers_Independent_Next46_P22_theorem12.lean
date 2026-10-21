-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_theorem12
-- name    : QAlgorithms.Papers.Independent.Next46.P22.theorem12
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:52:47.735317+00:00
-- url     : https://prove2.me/theorems/4e37a078-f102-4e61-9e98-5105c26388a9
-- title:
--   Theorem 12
-- statement:
--   Let $F$ have characteristic zero, $H$ be a Hopf algebra with a normalized ad-invariant left integral and $L$ a finite-dimensional right $H$-comodule Lie algebra. Suppose its actual radicals $R=\operatorname{rad}(L)$ and $N=\operatorname{nilrad}(L)$ are subcomodules. For each given semisimple subcomodule Lie subalgebra $B$ with $L=B\oplus R$, there exists an invariant subspace $S$ with
--
--   $$R=S\oplus N,\qquad [B,S]=0,\qquad L=B\oplus S\oplus N.$$
--
--   The same supplied $B$ occurs in the conclusion, and $S$ is only a subspace. All sums are internal vector-space sums. This refines every given invariant Levi complement under the general-H hypotheses.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 14, Theorem 12

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Theorem 12, PDF p.14: for each GIVEN semisimple invariant complement B,
produce S. Stability of both actual radicals is assumed in this general-H version. -/
theorem theorem12 [CharZero F] [FiniteDimensional F L]
    (rho : RightComodule F H L) (hr : ComoduleLie rho)
    (t : H →ₗ[F] F) (ht : NormalizedAdIntegral t)
    (hR : CoStable rho (LieAlgebra.radical F L).toSubmodule)
    (hN : CoStable rho (lieNilpotentRadical F L).toSubmodule)
    (B : LieSubalgebra F L) (hB : Semisimple F B) (hBi : CoStable rho B.toSubmodule)
    (hBR : IsCompl B.toSubmodule (LieAlgebra.radical F L).toSubmodule) :
    ∃ S : Submodule F L, CoStable rho S ∧ SplitsRadical S ∧
      (∀ b ∈ B, ∀ s ∈ S, ⁅b, s⁆ = 0) ∧
      IsCompl B.toSubmodule (S ⊔ (lieNilpotentRadical F L).toSubmodule) := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
