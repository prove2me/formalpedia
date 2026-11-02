-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P58_d3_tip_expansion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P58.d3_tip_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:56:26.25006+00:00
-- url     : https://prove2.me/theorems/29f3a6ec-70da-48fb-9fbd-d8e40095cad9
-- title:
--   Regular D3 cylinder endpoint expansion
-- statement:
--   In the dimensionless compactified D3 reduced model, fix an endpoint radius $r_0>0$. There exists a regular cylinder profile $r:[0,1]\to\mathbb R$ anchored at the boundary $z=0$, with $r(1)=r_0$, satisfying the Euler–Lagrange equation of $\int r z^{-3}\sqrt{1+(1-z^4)r'^2}\,dz$. Its regulated areas are finite and
--
--   $$
--   r(z)=r_0+\frac{1-z}{4r_0}+o(1-z),\qquad z\to1^-.
--   $$
--
--   This supplies regular endpoint data for the shooting family. The singular joining limit $r_0=0$ is excluded.
-- source:
--   Topological Entanglement Entropy and Holography, arXiv:0805.1891v2, PDF p. 11, (3.20)–(3.21)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P58

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P58

open Set Filter MeasureTheory

open scoped Topology

/-- PDF p.11, (3.20)--(3.21): regular D3 cylinders exist and have the
stated endpoint expansion. The divided formula excludes the singular r0=0 limit. -/
theorem d3_tip_expansion (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ r : ℝ → ℝ, IsCylinder .d3 (r 0) r ∧ r 1 = r0 ∧
      Asymptotics.IsLittleO (nhdsWithin (1 : ℝ) (Iio 1))
        (fun z => r z - r0 - (1 - z) / (4 * r0)) (fun z => 1 - z) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P58

end
