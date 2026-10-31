-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P15_sittingPath_concatenate
-- name    : QAlgorithms.Papers.Independent.Intake100.P15.sittingPath_concatenate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:16:46.342469+00:00
-- url     : https://prove2.me/theorems/a8cab5ac-3a8b-4e88-bd40-a33deacc513a
-- title:
--   Lemma 4.1: concatenation of diffeological sitting paths
-- statement:
--   Let $X$ be any diffeological space, and let $\gamma_1,\gamma_2:[0,1]\to X$ be diffeologically smooth paths with sitting instants and $\gamma_1(1)=\gamma_2(0)$. Then their concatenation is again a diffeologically smooth path with sitting instants:
--
--   $$
--   (\gamma_2\circ\gamma_1)(t)=
--   \begin{cases}\gamma_1(2t),&t<\tfrac12,\\
--   \gamma_2(2t-1),&t\ge\tfrac12.
--   \end{cases}
--   $$
--
--   This supplies the composition operation used in the diffeological path groupoid.
--
--   **Formalization Note** Paths are represented by their constant sitting extensions to $\mathbb R$. The two paths may have different sitting instants. The assertion concerns every diffeological space, including spaces without an underlying manifold.
-- source:
--   Smooth Functors vs. Differential Forms, arXiv:0802.0663v4, PDF p. 50, Lemma 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P15

namespace QAlgorithms.Papers.Independent.Intake100.P15

open scoped Manifold ContDiff

universe u v w z

/-- Lemma 4.1, PDF p. 50. Concatenating composable sitting
paths in any diffeological space gives a sitting path. No manifold or
uniform sitting instant for a family of paths is assumed. -/
theorem sittingPath_concatenate
    {X : Type u} [DiffeologicalSpace X]
    (gammaOne gammaTwo : ℝ → X)
    (hOne : IsSittingPath gammaOne) (hTwo : IsSittingPath gammaTwo)
    (hJoin : gammaOne 1 = gammaTwo 0) :
    IsSittingPath (sittingPathConcat gammaTwo gammaOne) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P15
