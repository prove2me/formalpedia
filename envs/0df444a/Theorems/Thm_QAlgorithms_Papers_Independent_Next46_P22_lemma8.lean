-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_lemma8
-- name    : QAlgorithms.Papers.Independent.Next46.P22.lemma8
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:48:52.641031+00:00
-- url     : https://prove2.me/theorems/1fa2ff29-0e20-4967-9fb9-18cd43969eb6
-- title:
--   Lemma 8
-- statement:
--   Let $F$ be any field, $H$ any Hopf algebra, $L$ a right $H$-comodule Lie algebra, and $V,W$ compatible $(H,L)$-modules. Let $\pi:V\to W$ be an $F$-linear $L$-module homomorphism and $t:H\to F$ an ad-invariant left integral. With antipode $\mathcal S$, the function
--
--   $$\widetilde\pi(x)=\sum t\bigl((\pi(x_0))_1\mathcal S(x_1)\bigr)(\pi(x_0))_0$$
--
--   is linear, $H$-colinear and $L$-linear. If $t(1)=1$, $W$ is a simultaneous submodule and subcomodule of $V$ with its induced structures, and $\pi$ restricts to the identity on $W$, then so does $\widetilde\pi$. An injective compatible inclusion represents the literal subspace inclusion. Neither symmetry nor normalization is assumed in the first clause.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 12, Lemma 8

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

/-- Lemma 8, PDF p.12: averaging is colinear and L-linear. An injective compatible
inclusion W→V expresses the literal submodule inclusion with induced structures
in the additional projection clause. No symmetry or normalization in the first clause. -/
theorem lemma8 (rhoL : RightComodule F H L) (hr : ComoduleLie rhoL)
    (rhoV : RightComodule F H V) (hV : CoCompatible rhoL rhoV)
    (rhoW : RightComodule F H W) (hW : CoCompatible rhoL rhoW)
    (pi : V →ₗ[F] W) (hpi : LieIntertwiner (L := L) pi)
    (t : H →ₗ[F] F) (ht : LeftIntegral t) (had : AdInvariant t) :
    LinearFunction (F := F) (hopfAverage rhoV rhoW t pi) ∧ Colinear rhoV rhoW (hopfAverage rhoV rhoW t pi) ∧
    LieIntertwiner (L := L) (hopfAverage rhoV rhoW t pi) ∧
    ∀ incl : W →ₗ[F] V, Function.Injective incl →
      Colinear rhoW rhoV incl → LieIntertwiner (L := L) incl → t 1 = 1 →
      (∀ w, pi (incl w) = w) → ∀ w, hopfAverage rhoV rhoW t pi (incl w) = w := by sorry

end LieModules

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
