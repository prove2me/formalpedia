-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P71_measurementChannel_properties
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P71.measurementChannel_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:58:52.994765+00:00
-- url     : https://prove2.me/theorems/be6a2bd4-6526-4231-b8d7-cb28988b299e
-- title:
--   Measurement-channel and inverse properties
-- statement:
--   Fix a Borel probability ensemble of unitaries on $N$ qudits of dimension $d\ge2$. Write $\nu$ for the prior law of $S=U^\dagger|b\rangle\langle b|U$, with $b$ uniform independently of $U$, and $\mathcal M(X)=d^N\mathbb E_\nu[S\operatorname{Tr}(SX)]$. The prior is a probability measure, each Born-weighted posterior for a density matrix is a probability measure, and the polynomial moment integrands are integrable. The snapshot map is continuous. The channel is completely positive, trace-preserving and self-adjoint:
--
--   $$\operatorname{Tr}\mathcal M(X)=\operatorname{Tr}X,\qquad \operatorname{Tr}(X^\dagger\mathcal M(Y))=\operatorname{Tr}(\mathcal M(X)^\dagger Y).$$
--
--   If $\mathcal M$ is injective, its inverse is also trace-preserving and self-adjoint. Local scrambling and completeness are unnecessary for the forward-channel assertions. This separates the measurement experiment's validity from the assumptions needed for inversion.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, PDF p. 3, §II A, Eq.(3): measurement-channel properties

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P71

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Intakethird100.P71

attribute [local instance] Classical.propDecidable

local notation "Config" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Config (P := Fin n) (fun _ => d)

local notation "Op" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Op (Config n d)

attribute [local instance] QAlgorithms.Papers.Independent.Intakethird100.P71.matrixContinuousENorm

local notation "Unitary" n:max d:max => Matrix.unitaryGroup (Config n d) ℂ

local notation "Local" n:max d:max => Fin n → Matrix.unitaryGroup (Fin d) ℂ

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF pp.3–4 Eq.(3): the forward measurement channel is CPTP and self-adjoint,
without local scrambling or completeness. Its inverse, when complete, is
trace-preserving and self-adjoint. Polynomial integrability and Born-law
normalization are conclusions from the projective construction. -/
theorem measurementChannel_properties {n d : ℕ} (hd : 2 ≤ d) (E : ProjectiveEnsemble n d) :
    IsProbabilityMeasure (prior E) ∧ SnapshotPolynomialIntegrable (prior E) ∧
    (∀ b, Continuous (fun U : Unitary n d => raw U b)) ∧
    (∀ rho : Op n d, IsDensityMatrix rho → IsProbabilityMeasure (posteriorOf (prior E) rho)) ∧
    QAlgorithms.IsChannel (snapshotMeasurementMap (prior E)) ∧
    (∀ X : Op n d, (snapshotMeasurementMap (prior E) X).trace = X.trace) ∧
    (∀ X Y : Op n d, (Xᴴ * snapshotMeasurementMap (prior E) Y).trace =
      ((snapshotMeasurementMap (prior E) X)ᴴ * Y).trace) ∧
    (∀ hc : Complete (prior E),
      (∀ X : Op n d, (snapshotInverse (prior E) hc X).trace = X.trace) ∧
      (∀ X Y : Op n d, (Xᴴ * snapshotInverse (prior E) hc Y).trace =
        ((snapshotInverse (prior E) hc X)ᴴ * Y).trace)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P71

end
