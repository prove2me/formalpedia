-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_ideal_graph_rule_limits
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.ideal_graph_rule_limits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:47:25.372488+00:00
-- url     : https://prove2.me/theorems/dea224f1-7b18-4f89-a3ab-f4d26aff071d
-- title:
--   III.E: recovery of earlier ideal real-graph rules where both limits are finite
-- statement:
--   Let valid Gaussian graphs $Z(s)$ tend to a finite real symmetric graph $V$ as $s\to+\infty$. Fix a real symplectic block matrix $\begin{psmallmatrix}A&B\\C&D\end{psmallmatrix}$, and suppose $A+BV$ is invertible. Then
--
--   $$(C+DZ(s))(A+BZ(s))^{-1}\longrightarrow (C+DV)(A+BV)^{-1}.$$
--
--   Every coordinate-selected principal submatrix has the corresponding limit. This covers the displayed unitary rules and deletion after them wherever the rational final graph stays finite, including the nonsingular double-Fourier rule. It makes no continuity claim about a singular totalized inverse.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 12, III.E: recovery of earlier ideal real-graph rules where both limits are finite

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.12–13: the explicit graph rules pass to finite real limits.
The nonzero real denominator is the finiteness guard for the rational rules;
no continuity at a singular totalized inverse is asserted. Principal submatrices
also converge, covering deletion after the explicit unitary graph updates. -/
theorem ideal_graph_rule_limits {I : Type*} [Fintype I] [DecidableEq I]
    (Z : ℝ → Matrix I I ℂ) (V : Matrix I I ℝ) (hV : V.IsSymm)
    (hZ : ∀ s, ValidGraph (Z s)) (hlim : Tendsto Z atTop (nhds (complexify V)))
    (A B C D : Matrix I I ℝ) (hS : graphBlockSymplectic A B C D)
    (hFinite : IsUnit (A + B * V).det) :
    Tendsto (fun s => mobius A B C D (Z s)) atTop
      (nhds (complexify ((C + D * V) * (A + B * V)⁻¹))) ∧
    (∀ (m : ℕ) (select : Fin m → I), Function.Injective select →
      Tendsto (fun s => (mobius A B C D (Z s)).submatrix select select) atTop
        (nhds (complexify (((C + D * V) * (A + B * V)⁻¹).submatrix select select)))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
