-- Prove2me | Theorems.Thm_PolygonalPathFiniteChainConcat
-- name    : PolygonalPathFiniteChainConcat
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:55:42.663989+00:00
-- url     : https://prove2.me/theorems/364396cb-957f-4ef5-b3e0-b16d3dd71e4b
-- title:
--   Finite polygonal path chain concatenation
-- statement:
--   A finite list of polygonal paths with matching consecutive endpoints and carriers in a common set can be concatenated into one polygonal path joining the first source to the last target and remaining in that set.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/PolygonalPathFiniteChainConcat.lean#L1-L63

import Definitions.Def_PolygonalPath

open Classical
noncomputable section

lemma PolygonalPathFiniteChainConcat
    (S : Set (EuclideanSpace ℝ (Fin 2))) :
    ∀ (pieces : List PolygonalPath) (first last : PolygonalPath),
      pieces.head? = some first →
        pieces.getLast? = some last →
          (∀ η : PolygonalPath, η ∈ pieces → η.carrier ⊆ S) →
            (∀ (i : ℕ) (hi : i + 1 < pieces.length),
              (pieces[i]).target = (pieces[i + 1]).source) →
              ∃ ζ : PolygonalPath,
                ζ.source = first.source ∧
                  ζ.target = last.target ∧
                    ζ.carrier ⊆ S := by sorry
