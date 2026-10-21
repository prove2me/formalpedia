-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_lemma5
-- name    : QAlgorithms.Papers.Independent.Next46.P22.lemma5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:43:12.696126+00:00
-- url     : https://prove2.me/theorems/1da43ce9-63d8-469e-bb60-fe68c560d087
-- title:
--   Lemma 5
-- statement:
--   Let $F$ have characteristic zero, $H$ be a Hopf algebra with a normalized ad-invariant left integral $t$, and $L$ a finite-dimensional semisimple right $H$-comodule Lie algebra. Let $V$ be a finite-dimensional symmetric $(H,L)$-module. Every colinear alternating two-cocycle $\omega$ is the coboundary of a colinear linear one-cochain $\nu$:
--
--   $$d\omega=0\ \Longrightarrow\ \exists\nu\in\widetilde C^1(L;V),\quad d\nu=\omega;\qquad\widetilde H^2(L;V)=0.$$
--
--   The differentials use $d\nu(x,y)=x\cdot\nu(y)-y\cdot\nu(x)-\nu([x,y])$. This is the vanishing assertion, expressed without presupposing a lifting property.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 8, Lemma 5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

section LieModules

variable [LieRingModule L V] [LieModule F L V] [LieRingModule L W] [LieModule F L W]

/-- Lemma 5, PDF pp.8–9: zero second colinear cohomology, equivalently every
colinear two-cocycle is d of a colinear one-cochain; no lifting is assumed. -/
theorem lemma5 [CharZero F] [FiniteDimensional F L] [FiniteDimensional F V]
    (hL : Semisimple F L) (rhoL : RightComodule F H L) (hr : ComoduleLie rhoL)
    (rhoV : RightComodule F H V) (hs : SymmetricComodule rhoL rhoV)
    (t : H →ₗ[F] F) (ht : NormalizedAdIntegral t) :
    ∀ omega : LieModule.Cohomology.twoCochain F L V,
      omega ∈ LieModule.Cohomology.twoCocycle F L V → ColinearTwo rhoL rhoV omega →
      ∃ nu : L →ₗ[F] V, Colinear rhoL rhoV nu ∧
        LieModule.Cohomology.d₁₂ F L V nu = omega := by sorry

end LieModules

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
