-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_werner_region_rotated_cubes
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.werner_region_rotated_cubes
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T14:06:00.956921+00:00
-- url     : https://prove2.me/theorems/000b16bd-fbf7-4f00-83d2-486467fe34d4
-- title:
--   Sec. III C, unnumbered: bicone as intersection of rotated physical cubes
-- statement:
--   Let $d\ge3$, and let $x=(a,b,c)\in\mathbb R^3$ be Werner swap coordinates. Let $R_\theta$ be rotation by $\theta$ about the line through the origin in direction $(1,1,1)$. Then
--   $$x\text{ lies in the Werner bicone of Theorem III.1}\quad\Longleftrightarrow\quad R_\theta x\in[-1,1]^3\ \text{for every }\theta\in\mathbb R.$$
--   Under the agreement-coordinate change $\alpha=(1+\psi)/(d+1)$, this is the source's intersection of rotated physical cubes.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 9, Sec. III C, unnumbered: bicone as intersection of rotated physical cubes

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Sec.III C, PDF p.9: in d>=3, the Werner region is the intersection of the
physical cubes rotated about the diagonal through the origin. -/
theorem werner_region_rotated_cubes (d : ℕ) (hd : 3 ≤ d) (x : Fin 3 → ℝ) :
    wernerRegion d (x 0) (x 1) (x 2) ↔
      ∀ theta : ℝ, ∀ i : Fin 3, -1 ≤ diagonalAxisRotation theta x i ∧ diagonalAxisRotation theta x i ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
