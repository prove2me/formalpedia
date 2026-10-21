-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_lemma4
-- name    : QAlgorithms.Papers.Independent.Next46.P22.lemma4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:42:30.881455+00:00
-- url     : https://prove2.me/theorems/d1569ca5-a1cf-436d-9b78-8c6395a9e24e
-- title:
--   Lemma 4
-- statement:
--   Let $H$ be any Hopf algebra over a field $F$, $V,W$ right $H$-comodules, $r:V\to W$ an $F$-linear map and $t:H\to F$ a left integral. Write $\mathcal S$ for the antipode. The explicitly defined function
--
--   $$\widetilde r(x)=\sum t\bigl((r(x_0))_1\mathcal S(x_1)\bigr)(r(x_0))_0$$
--
--   is $F$-linear and $H$-colinear. If additionally $t(1)=1$ and a colinear linear map $\pi:W\to V$ satisfies $\pi\circ r=\operatorname{id}_V$, then $\pi\circ\widetilde r=\operatorname{id}_V$. Normalization is confined to this additional clause; ad-invariance is not assumed.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 7, Lemma 4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Lemma 4, PDF pp.7–8: explicit averaging is linear and colinear. Only the
additional right-inverse clause assumes normalization; no ad-invariance is needed. -/
theorem lemma4 (rhoV : RightComodule F H V) (rhoW : RightComodule F H W)
    (r : V →ₗ[F] W) (t : H →ₗ[F] F) (ht : LeftIntegral t) :
    LinearFunction (F := F) (hopfAverage rhoV rhoW t r) ∧ Colinear rhoV rhoW (hopfAverage rhoV rhoW t r) ∧
    ∀ pi : W →ₗ[F] V, Colinear rhoW rhoV pi → (∀ x, pi (r x) = x) → t 1 = 1 →
      ∀ x, pi (hopfAverage rhoV rhoW t r x) = x := by sorry

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
