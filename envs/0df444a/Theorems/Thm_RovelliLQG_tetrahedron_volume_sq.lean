-- Prove2me | Theorems.Thm_RovelliLQG_tetrahedron_volume_sq
-- name    : RovelliLQG.tetrahedron_volume_sq
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T19:28:05.779983+00:00
-- url     : https://prove2.me/theorems/c5b833ba-4fc7-463b-9bb8-76dac94209c6
-- title:
--   Eq. (10): squared tetrahedron volume from three face area vectors
-- statement:
--   Let $p_0,p_1,p_2,p_3\in\mathbb R^3$ and let $T=\operatorname{conv}\{p_0,p_1,p_2,p_3\}$, with volume $V$. For the three faces through $p_0$, define the **face area vectors**
--   $$L_1=\tfrac12(p_1-p_0)\times(p_2-p_0),\quad L_2=\tfrac12(p_2-p_0)\times(p_3-p_0),\quad L_3=\tfrac12(p_3-p_0)\times(p_1-p_0),$$
--   each orthogonal to its face and of length equal to the face's area. Then
--   $$V^2=\tfrac29\,\big|L_1\cdot(L_2\times L_3)\big|.$$
--
--   This is the exact Euclidean form of the review's eq. (10), $V_n^2=|\vec L_{l_1}\cdot(\vec L_{l_2}\times\vec L_{l_3})|$, which expresses the volume of a quantum tetrahedron through its area vectors (the review drops the constant $2/9$). Degenerate (flat) tetrahedra are included; both sides then vanish.
--
--   **Formalization Note** $V$ is the Lebesgue measure of the convex hull, converted to a real number.
-- source:
--   C. Rovelli, Loop quantum gravity: the first 25 years, Class. Quantum Grav. 28 (2011) 153002, doi:10.1088/0264-9381/28/15/153002, arXiv:1012.4707, §2.1, p. 5, eq. (10) (volume of a 4-valent node; the review omits the numerical constant)

import Mathlib
import Definitions.Def_RovelliLQG_Defs

open scoped InnerProductSpace

namespace RovelliLQG

theorem tetrahedron_volume_sq (p₀ p₁ p₂ p₃ : E3) :
    (MeasureTheory.volume (convexHull ℝ {p₀, p₁, p₂, p₃})).toReal ^ 2 =
      (2 / 9 : ℝ) * |⟪(1 / 2 : ℝ) • cross3 (p₁ - p₀) (p₂ - p₀),
        cross3 ((1 / 2 : ℝ) • cross3 (p₂ - p₀) (p₃ - p₀))
          ((1 / 2 : ℝ) • cross3 (p₃ - p₀) (p₁ - p₀))⟫_ℝ| := by
  sorry

end RovelliLQG
