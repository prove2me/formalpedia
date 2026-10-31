-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_canonical_cluster_family
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.canonical_cluster_family
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:39:29.968994+00:00
-- url     : https://prove2.me/theorems/1e78f5f1-0edb-4458-ac7c-a7664bc66bb3
-- title:
--   II.F: canonical finite-squeezing cluster family, Eqs. (2.28)–(2.30)
-- statement:
--   Let $A$ be any finite real symmetric adjacency matrix and $r\in\mathbb R$. Starting with vacuum and applying momentum squeezing followed by the controlled-$Z$ preparation gives the valid graph
--
--   $$Z_r=A+i e^{-2r}I,\qquad \operatorname{cov}(p-Aq)=\tfrac12 e^{-2r}I.$$
--
--   As $r\to+\infty$, $Z_r\to A$ and the displayed nullifier covariance tends to zero. Both limits are finite matrix limits, and make no assertion of a normalized ideal infinite-squeezing state.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 7, II.F: canonical finite-squeezing cluster family, Eqs. (2.28)–(2.30)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.7, (2.28)–(2.30): canonical preparation and graph limit.
Only matrices converge; no ideal normalized state is asserted. -/
theorem canonical_cluster_family {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (hA : A.IsSymm) :
    (∀ r : ℝ, ValidGraph (canonicalGraph A r) ∧
      mobius ((Real.exp r) • 1) 0 ((Real.exp r) • A) ((Real.exp (-r)) • 1)
        (Complex.I • 1) = canonicalGraph A r ∧
      targetError (canonicalGraph A r) A = (Real.exp (-2 * r) / 2) • 1) ∧
    Tendsto (canonicalGraph A) atTop (nhds (complexify A)) ∧
    Tendsto (fun r => targetError (canonicalGraph A r) A) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
