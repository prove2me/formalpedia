-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_second_cluster_family
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.second_cluster_family
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:40:14.420395+00:00
-- url     : https://prove2.me/theorems/2a0a9880-9f38-47af-a4b4-a6ce4895e480
-- title:
--   II.F: second family with the same ideal graph, Eq. (2.31)
-- statement:
--   For any finite real symmetric $A$ and real $\alpha$, define $c=\cosh(2\alpha)$ and $t=\tanh(2\alpha)$. The alternative finite Gaussian cluster family is valid and satisfies
--
--   $$Z_\alpha=tA+i c^{-1}I,\qquad \operatorname{cov}(p-Aq)=\frac{I}{2c}+\frac{c(t-1)^2}{2}A^2.$$
--
--   As $\alpha\to+\infty$, the graph tends to $A$ and this fixed-$A$ error tends to zero. No self-inverse or bipartite assumption on $A$ is needed. The fixed-target error establishes the cluster approximation, beyond graph convergence alone.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 7, II.F: second family with the same ideal graph, Eq. (2.31)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.7, (2.31): the second physical approximating family, including
the fixed-target nullifier error required by (2.3), not graph convergence alone. -/
theorem second_cluster_family {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsSymm) :
    (∀ alpha : ℝ, ValidGraph (sechGraph A alpha) ∧
      targetError (sechGraph A alpha) A =
        ((Real.cosh (2 * alpha))⁻¹ / 2) • 1 +
        ((Real.tanh (2 * alpha) - 1) ^ 2 * Real.cosh (2 * alpha) / 2) • (A * A)) ∧
    Tendsto (sechGraph A) atTop (nhds (complexify A)) ∧
    Tendsto (fun alpha => targetError (sechGraph A alpha) A) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
