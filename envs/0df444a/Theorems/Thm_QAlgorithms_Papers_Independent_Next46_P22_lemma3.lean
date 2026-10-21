-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_lemma3
-- name    : QAlgorithms.Papers.Independent.Next46.P22.lemma3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:42:01.737988+00:00
-- url     : https://prove2.me/theorems/5139061d-e4cf-494b-90f1-98cdabc14a73
-- title:
--   Lemma 3
-- statement:
--   Let $F$ be any field, $H$ any Hopf algebra, $L$ a right $H$-comodule Lie algebra and $V$ a symmetric $(H,L)$-module. Symmetry requires the coaction compatibility for both coefficient orders $a_1v_1$ and $v_1a_1$. For every colinear linear one-cochain $\omega:L\to V$, its alternating coboundary is colinear:
--
--   $$(d\omega)(x,y)=x\cdot\omega(y)-y\cdot\omega(x)-\omega([x,y]),\qquad d(\widetilde C^1(L;V))\subseteq\widetilde C^2(L;V).$$
--
--   Here a colinear two-cochain has coaction coefficient $x_1y_1$ in that order. The symmetry hypothesis is retained even when $H$ is noncommutative; no integral is assumed.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 7, Lemma 3

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

/-- Lemma 3, PDF p.7: closure under d for symmetric coefficients, without
commutative H or any integral assumption. -/
theorem lemma3 (rhoL : RightComodule F H L) (hr : ComoduleLie rhoL)
    (rhoV : RightComodule F H V) (hs : SymmetricComodule rhoL rhoV)
    (omega : L →ₗ[F] V) (ho : Colinear rhoL rhoV omega) :
    ColinearTwo rhoL rhoV (LieModule.Cohomology.d₁₂ F L V omega) := by sorry

end LieModules

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
