-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P05_spectral_isolated_eigenvalue
-- name    : QAlgorithms.Papers.Independent.Claimed50.P05.spectral_isolated_eigenvalue
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:23:39.798273+00:00
-- url     : https://prove2.me/theorems/056b60d4-d921-4aee-846b-37d041153750
-- title:
--   §7.1 and §7.3, unnumbered: isolated spectral points are eigenvalues
-- statement:
--   Let $A$ be a closed densely defined normal operator on a $k$-Hilbert space, self-adjoint in the real case. If $\lambda\in\sigma(A)$ is isolated in the spectrum, meaning there is an $\varepsilon>0$ with $\sigma(A)\cap B(\lambda,\varepsilon)=\{\lambda\}$, then
--
--   $$\lambda\in\sigma_p(A).$$
--
--   The spectral-membership assumption is explicit; isolation is relative to the spectrum.
--
--   This extends the isolated-point eigenvalue conclusion to unbounded operators.
-- source:
--   The Functional Calculus Approach to the Spectral Theorem, arXiv:2003.06130v2, PDF p. 32, §7.1 and §7.3, unnumbered: isolated spectral points are eigenvalues

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P05

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory

open scoped Topology ENNReal InnerProductSpace

namespace QAlgorithms.Papers.Independent.Claimed50.P05

universe u v w

variable {k : Type*} [RCLike k]

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace k H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace k K] [CompleteSpace K]

/-- Sections 7.1 and 7.3, PDF pp.32,35: isolated spectral points of admissible operators are eigenvalues. -/
theorem spectral_isolated_eigenvalue (A : Relation H) (hA : SpectralAdmissible (k := k) A)
    (z : k) (hz : z ∈ spectrumOf (k := k) A)
    (hisolated : ∃ e : ℝ, 0 < e ∧ ∀ w ∈ spectrumOf (k := k) A, dist w z < e → w = z) :
    z ∈ pointSpectrum (k := k) A := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P05

end
