-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_one_node_entanglement
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.one_node_entanglement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:52:32.047219+00:00
-- url     : https://prove2.me/theorems/54f86c89-644b-4b92-9a4a-01bbf40d66bd
-- title:
--   IV.G: one-node entanglement from incident weights
-- statement:
--   Let $V$ be a real symmetric graph, let $r$ be finite real squeezing, and let $k$ be a node of the canonical pure state with graph $V+i e^{-2r}I$. Its reduced one-mode covariance has the single symplectic eigenvalue
--
--   $$\sigma_k=\tfrac12\sqrt{1+e^{4r}\sum_{l\ne k}V_{kl}^2}.$$
--
--   The actual global Gaussian wavefunction factors into square-integrable wavefunctions on $k$ and its complement exactly when all $V_{kl}$ with $l\ne k$ vanish. Equivalently, $\sigma_k>1/2$ exactly when at least one off-diagonal incident link is nonzero. This characterizes entanglement of node $k$ with the rest, including the unentangled one-mode case.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 18, IV.G: one-node entanglement from incident weights

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.18, (4.40)–(4.41): one node versus its entire complement.
Nonzero off-diagonal incident weights give entanglement of this pure global
state, not pairwise entanglement of each edge. Self-loops have no effect. -/
theorem one_node_entanglement (N : ℕ) (V : Matrix (Fin N) (Fin N) ℝ)
    (hV : V.IsSymm) (r : ℝ) (k : Fin N) :
    let Z := canonicalGraph V r
    let pick : Phase 1 → Phase N := Sum.map (fun _ => k) (fun _ => k)
    let f := gaussianWave ((Real.exp (-2*r)) • 1) (-V)
    HasSymplecticSpectrum ((graphCovariance Z).submatrix pick pick) (fun _ => nodeSpectrum V r k) ∧
    (FactorsAt f k ↔ ∀ l : Fin N, l ≠ k → V k l = 0) ∧
    ((1/2 : ℝ) < nodeSpectrum V r k ↔ ∃ l : Fin N, l ≠ k ∧ V k l ≠ 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
