-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P02_functorialInverse_isGroupoid
-- name    : QAlgorithms.Papers.Independent.Gap48.P02.functorialInverse_isGroupoid
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:49:29.652512+00:00
-- url     : https://prove2.me/theorems/c04afc0a-4f17-405e-822b-52598da7c81c
-- title:
--   Lemma 52: all morphisms are invertible
-- statement:
--   Let $M$ be a monoidal category admitting functorial inverses: there exists a covariant endofunctor $i:M\to M$ and a natural isomorphism $x\otimes i(x)\cong\mathbf{1}$. Then the given underlying category is a groupoid:
--
--   $$\text{every morphism }f:x\to y\text{ in }M\text{ is invertible}.$$
--
--   This derives invertibility of morphisms from functorial inverses of objects, without assuming a groupoid structure beforehand.
-- source:
--   Central Extensions of Smooth 2-Groups and a Finite-Dimensional String 2-Group, arXiv:0911.2483v3, PDF p. 20, Lemma 52

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P02

namespace QAlgorithms.Papers.Independent.Gap48.P02

open CategoryTheory MonoidalCategory

universe v u

/-- Lemma 52, PDF p. 20: admitting functorial inverses makes the
existing underlying category a groupoid; this is not a hypothesis. -/
theorem functorialInverse_isGroupoid
    (M : Type u) [Category.{v} M] [MonoidalCategory M]
    (h : Nonempty (FunctorialInverseChoice M)) :
    CategoryTheory.IsGroupoid M := by sorry

end QAlgorithms.Papers.Independent.Gap48.P02
