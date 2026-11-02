-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P58_d4_tip_expansion
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P58.d4_tip_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:57:33.713068+00:00
-- url     : https://prove2.me/theorems/0fa2cb46-9eae-43f2-ab3a-c39a1691aacc
-- title:
--   D4 regular tip expansion and its actual inverse
-- statement:
--   In the dimensionless D4 reduced model, fix $r_0>0$. There exists a regular cylinder inverse profile $r(z)$ solving the variational equation of $\int r^2z^{-3}\sqrt{1+z(1-z^3)r'^2}\,dz$, with $r(1)=r_0$. Let $z(t)$ be the actual inverse on the range of this strictly decreasing graph. Then
--
--   $$
--   r(z)=r_0+\frac{2}{3r_0}(1-z)+o(1-z)\quad(z\to1^-),
--   $$
--
--   and
--
--   $$
--   z(t)=1-\frac32r_0(t-r_0)+o(t-r_0)\quad(t\to r_0^+).
--   $$
--
--   The two slopes are reciprocal, and the zero-radius singular joining limit is excluded. These formulas are regular tip data, not entropy-minimality statements.
-- source:
--   Topological Entanglement Entropy and Holography, arXiv:0805.1891v2, PDF p. 16, (4.13)–(4.14)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P58

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P58

open Set Filter MeasureTheory

open scoped Topology

/-- PDF p.16, (4.13)--(4.14): the D4 tip expansion and the reciprocal
expansion of its actual inverse. The endpoint radius is positive. -/
theorem d4_tip_expansion (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ r : ℝ → ℝ, IsCylinder .d4 (r 0) r ∧ r 1 = r0 ∧
      Asymptotics.IsLittleO (nhdsWithin (1 : ℝ) (Iio 1))
        (fun z => r z - r0 - 2 * (1 - z) / (3 * r0)) (fun z => 1 - z) ∧
      Asymptotics.IsLittleO (nhdsWithin r0 (Ioi r0))
        (fun t => height r 1 t - 1 + (3 : ℝ) / 2 * r0 * (t - r0))
        (fun t => t - r0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P58

end
