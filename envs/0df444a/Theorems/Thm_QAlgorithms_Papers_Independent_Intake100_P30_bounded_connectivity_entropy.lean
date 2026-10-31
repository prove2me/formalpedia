-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_bounded_connectivity_entropy
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.bounded_connectivity_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:52:55.466702+00:00
-- url     : https://prove2.me/theorems/bcf42182-2de5-4096-9bac-102d5074fed0
-- title:
--   IV.G: bounded one-node entropy at bounded degree
-- statement:
--   Fix finite real squeezing $r$, a degree bound $C\in\mathbb N$, and an entropy logarithm base $b>1$. Consider every finite real symmetric graph whose off-diagonal weights are zero or one, with at most $C$ neighbors at each node. Put $h_b(\sigma)=[(\sigma+1/2)\log(\sigma+1/2)-(\sigma-1/2)\log(\sigma-1/2)]/\log b$, the entropy of a one-mode Gaussian marginal. For every node $k$,
--
--   $$h_b(\sigma_k)\le h_b\!\left(\tfrac12\sqrt{1+e^{4r}C}\right).$$
--
--   Here $0\log0=0$. The bound is independent of graph size and concerns only node-versus-rest entropy, with $r,C,b$ fixed before the graph.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 18, IV.G: bounded one-node entropy at bounded degree

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.18: fixed squeezing and unit off-diagonal weights give an
entropy bound uniform over graph size. C is a degree bound, and b is any
chosen entropy base greater than 1. This is a node-versus-rest bound only. -/
theorem bounded_connectivity_entropy (b r : ℝ) (hb : 1 < b) (C : ℕ) :
    ∀ (N : ℕ) (V : Matrix (Fin N) (Fin N) ℝ), V.IsSymm →
      (∀ j l, j ≠ l → V j l = 0 ∨ V j l = 1) →
      (∀ j, (Finset.univ.filter (fun l => l ≠ j ∧ V j l ≠ 0)).card ≤ C) →
      ∀ k : Fin N,
        gaussianSpectralEntropy b (nodeSpectrum V r k) ≤
          gaussianSpectralEntropy b (Real.sqrt (1 + Real.exp (4*r) * (C : ℝ)) / 2) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
