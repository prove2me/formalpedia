-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P43_proposition2_bundle_category
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P43.proposition2_bundle_category
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:48:29.236877+00:00
-- url     : https://prove2.me/theorems/b5165d3b-3f73-4657-a2db-4ff82bca655c
-- title:
--   Arbitrary bundles and bundle maps form the slice category
-- statement:
--   Let $\mathcal C$ be any category and $B$ an object. A bundle over $B$ is an arbitrary arrow $p:E\to B$. A bundle map from $p:E\to B$ to $q:E'\to B$ is a map $f:E\to E'$ with $q\circ f=p$. These objects and morphisms form a category with
--
--   $$\operatorname{id}_p=\operatorname{id}_E,\qquad (f,f')\longmapsto f'\circ f.$$
--
--   This is the slice category $\mathcal C/B$. No local triviality, fibre or structure group is required.
-- source:
--   Higher gauge theory I: 2-Bundles, arXiv:math/0410328v3, PDF p. 11, Proposition 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P43

namespace QAlgorithms.Papers.Independent.Intakenext100.P43

open CategoryTheory CategoryTheory.Limits

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u v w

section Ordinary

variable {C : Type u} [Category.{v} C]

/-- Proposition 2, PDF p. 11: the prescribed commuting-triangle
morphisms, underlying-map composition and identities form a category.
The raw operations are fixed before asserting any category laws. -/
theorem proposition2_bundle_category (B : C) :
    ∃ cat : Category (Over B), cat.toCategoryStruct = bundleCategoryStruct B := by sorry

end Ordinary

end QAlgorithms.Papers.Independent.Intakenext100.P43
