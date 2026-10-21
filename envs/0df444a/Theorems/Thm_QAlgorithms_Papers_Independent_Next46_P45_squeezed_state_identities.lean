-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P45_squeezed_state_identities
-- name    : QAlgorithms.Papers.Independent.Next46.P45.squeezed_state_identities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:50:47.574577+00:00
-- url     : https://prove2.me/theorems/03361708-a79b-4eaa-85a7-424cae389ae0
-- title:
--   Squeezed-state EPR and entropy identities
-- statement:
--   For $r\ge0$, the Fock coefficients of $\Psi_s(r)=\cosh(r)^{-1}\sum_{N\ge0}\tanh(r)^N|N,N\rangle$ are square summable and the resulting vector has norm one. With $[X_j,P_j]=i$ and base-two spectral entropy,
--
--   $$\Delta(\Psi_s(r))=e^{-2r},\qquad E(\Psi_s(r))=\cosh^2r\log_2(\cosh^2r)-\sinh^2r\log_2(\sinh^2r).$$
--
--   Use $0\log_2 0=0$. For $r>0$ the uncertainty is strictly less than one. Every $0<\Delta<1$ is attained at the positive parameter $r_\Delta=-\frac12\ln\Delta$. At $r=0$ the formula gives the normalized vacuum, uncertainty one and zero entropy. These are identities of the actual vector and reduced-state spectral entropy, rather than definitions of entropy by a closed formula.
-- source:
--   Entanglement of formation for symmetric Gaussian states, arXiv:quant-ph/0304042v1, PDF p. 2, Unnumbered squeezed-state EPR and entropy identities, Eqs.(3)-(4) and text after Eq.(6)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P45

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (rankOne IsBarycenter)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance standardFormCovariance productWeyl
   CharacteristicSummable multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits InterleavedPhase)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF pp.1–2, (1),(3),(4) and the text after (6): actual normalized squeezed
vector, EPR level and spectral entropy identity. At r=0 the same formula is vacuum;
the strict Delta<1 statement is only for positive squeezing. -/
theorem squeezed_state_identities :
    (∀ r : ℝ, 0 ≤ r → Memℓp (squeezedCoefficients r) 2 ∧
      ‖squeezedVector r‖ = 1 ∧
      eprUncertainty (squeezedVector r) = Real.exp (-2 * r) ∧
      pureEntanglement (squeezedVector r) = ENNReal.ofReal
        (xlog2x (Real.cosh r ^ 2) - xlog2x (Real.sinh r ^ 2))) ∧
    (∀ r : ℝ, 0 < r → eprUncertainty (squeezedVector r) < 1) ∧
    (∀ delta : ℝ, 0 < delta → delta < 1 →
      0 < squeezingAt delta ∧ eprUncertainty (squeezedVector (squeezingAt delta)) = delta) := by sorry

end QAlgorithms.Papers.Independent.Next46.P45

end
