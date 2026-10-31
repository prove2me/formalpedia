-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_graph_gaussian_unique
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.graph_gaussian_unique
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:54:00.31448+00:00
-- url     : https://prove2.me/theorems/71021926-e986-4296-b62e-7296203db4ec
-- title:
--   Theorem A.2: every valid graph has a unique Gaussian pure state
-- statement:
--   Let $Z=V+iU$ be a finite complex symmetric matrix with $U>0$. The function
--
--   $$\psi_Z(q)=\pi^{-n/4}(\det U)^{1/4}\exp\!\left[-\tfrac12q^T(U-iV)q\right]$$
--
--   is a normalized Gaussian wavefunction with integrable quadrature forms and expectation-defined graph $Z$. It represents an actual norm-one vector of $L^2(\mathbb R^n)$. Every other normalized centered Gaussian vector with graph $Z$ equals $c\psi_Z$ for a complex scalar $c$ of modulus one. Thus every allowed graph specifies exactly one physical pure-state ray.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 20, Theorem A.2: every valid graph has a unique Gaussian pure state

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.20, Theorem A.2: every valid graph has an actual normalized
Gaussian L2 state, unique up to unit scalar phase. Explicit wavefunction and
expectation extraction prevent a contentless matrix-to-matrix correspondence. -/
theorem graph_gaussian_unique {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : ValidGraph Z) :
    let f := gaussianWave (imagPart Z) (-realPart Z)
    NormalizedGaussian f ∧ HasQuadratureForms f ∧ extractedGraph f = Z ∧
    ∃ psi : Schrodinger n, ‖psi‖ = 1 ∧ GaussianGraphRepresents Z psi ∧
      (fun q => psi q) =ᵐ[volume] f ∧
      ∀ phi : Schrodinger n, GaussianGraphRepresents Z phi →
        ∃ c : ℂ, ‖c‖ = 1 ∧ phi = c • psi := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
