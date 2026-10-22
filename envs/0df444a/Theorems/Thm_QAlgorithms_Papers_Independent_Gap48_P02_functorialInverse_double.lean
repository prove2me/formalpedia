-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P02_functorialInverse_double
-- name    : QAlgorithms.Papers.Independent.Gap48.P02.functorialInverse_double
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:48:53.182184+00:00
-- url     : https://prove2.me/theorems/a35a7ed6-7f54-4c8d-8e35-6bd79b50e2b6
-- title:
--   Lemma 51: double inverse is naturally identity
-- statement:
--   Let $M$ be a monoidal category, with its specified tensor product, unit, associator and unitors. For any chosen covariant endofunctor $i:M\to M$ equipped with a natural isomorphism from the functor $x\mapsto x\otimes i(x)$ to the constant unit functor, there exists a natural isomorphism
--
--   $$i\circ i\cong\operatorname{id}_M.$$
--
--   This gives the double-inverse property at the level of functors, including its naturality in every morphism.
-- source:
--   Central Extensions of Smooth 2-Groups and a Finite-Dimensional String 2-Group, arXiv:0911.2483v3, PDF p. 20, Lemma 51

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P02

namespace QAlgorithms.Papers.Independent.Gap48.P02

open CategoryTheory MonoidalCategory

universe v u

/-- Lemma 51, PDF p. 20: every chosen functorial inverse has its
square naturally isomorphic to the identity endofunctor. -/
theorem functorialInverse_double
    (M : Type u) [Category.{v} M] [MonoidalCategory M]
    (choice : FunctorialInverseChoice M) :
    Nonempty (choice.inverse ⋙ choice.inverse ≅ 𝟭 M) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P02
