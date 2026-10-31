-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_nullifier_covariances
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.nullifier_covariances
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:41:26.554571+00:00
-- url     : https://prove2.me/theorems/afa0a247-fb52-4965-8da5-e1c9a78984e6
-- title:
--   II.H: complex and real nullifier covariance and scalar error
-- statement:
--   Let $Z=V+iU$, where $V$ is real symmetric and $U$ is real symmetric positive definite, and let $\psi_Z$ be its normalized Gaussian wavefunction. The symmetrized complex-nullifier covariance and real-nullifier covariance are
--
--   $$\operatorname{cov}(p-Zq)=U,\qquad \operatorname{cov}(p-Vq)=\tfrac12 U,\qquad \sum_j\langle(p_j-\sum_kV_{jk}q_k)^2\rangle=\tfrac12\operatorname{tr}U.$$
--
--   The quadrature and nullifier forms used here are integrable. For an arbitrary real symmetric target $A$, the real-nullifier covariance equals $\tfrac12[U+(V-A)U^{-1}(V-A)]$. These identities quantify finite-squeezing error through squared-operator expectations, rather than squared means.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 8, II.H: complex and real nullifier covariance and scalar error

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF p.8, (2.40)–(2.42): covariance U for complex nullifiers,
U/2 for real nullifiers, and the sum of squared-operator expectations.
The arbitrary fixed target formula also makes (2.3)'s limiting meaning explicit. -/
theorem nullifier_covariances {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.PosDef) (hV : V.IsSymm) :
    let Z := complexify V + Complex.I • complexify U
    let f := gaussianWave U (-V)
    NormalizedGaussian f ∧ HasQuadratureForms f ∧
    complexNullifierCovariance Z f = complexify U ∧
    realNullifierCovariance V f = (1 / 2 : ℝ) • U ∧
    (∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsSymm →
      realNullifierCovariance A f = targetError Z A ∧
      targetError Z A = (1 / 2 : ℝ) • (U + (V - A) * U⁻¹ * (V - A))) ∧
    (∀ j k, Integrable (fun q => star (nullifier Z f j q) * nullifier Z f k q) ∧
      Integrable (fun q => star (nullifier (fun a b => star (Z a b)) f j q) *
        nullifier (fun a b => star (Z a b)) f k q) ∧
      Integrable (fun q => star (nullifier (complexify V) f j q) *
        nullifier (complexify V) f k q)) ∧
    Matrix.trace U / 2 = ∑ j, ∫ q, Complex.normSq (nullifier (complexify V) f j q) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
