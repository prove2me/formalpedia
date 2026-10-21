-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_qFunction_coherent_diagonal
-- name    : QAlgorithms.Papers.Independent.Next46.P17.qFunction_coherent_diagonal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:31:10.940269+00:00
-- url     : https://prove2.me/theorems/cdf949d0-009d-4852-961a-711de676e843
-- title:
--   Q function as the coherent-state diagonal, with corrected label
-- statement:
--   Let $n\geq1$ and let $\rho$ be an arbitrary normalized full $n$-mode state. Keep $D(\xi)=\exp(i\xi\cdot JR)$ and the Fourier definition (100) of $Q_\rho$. With $|0\rangle$ the joint vacuum, for every $\xi\in\mathbb R^{2n}$,
--
--   $$
--   Q_\rho(\xi)=(2\pi)^{-n}\langle D(-\xi)0|\rho|D(-\xi)0\rangle.
--   $$
--
--   The displayed expectation is real. **Source correction:** the printed coherent vector $D(\xi)|0\rangle$ is replaced by $D(-\xi)|0\rangle$, keeping the Weyl and Fourier signs unchanged. Comparison with (32), as in the source proof, fixes this sign.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 13, Appendix, coherent-state diagonal after (101), corrected coherent label

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17

noncomputable section

open Filter MeasureTheory

open scoped ENNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Next46.P17

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19 (productWeyl FiniteMeanEnergy PhysicalCovariance Cov FockIndex covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

/-- PDF p.13, Appendix, coherent-state diagonal identity after (101).
Printed: Q(xi)=(2*pi)^(-n)<xi|rho|xi>, with |xi>=D(xi)|0>.
Changed: the coherent vector is D(-xi)|0>, so its diagonal is the vacuum
entry of D(xi) rho D(xi)-adjoint. Only the coherent label changes.
Why: (25), (28), (32), and the Fourier sign in (100) fix this sign;
comparison with (32), as in the source proof, gives means +xi for that
projector. The Weyl action and Fourier Q definition are kept exactly.
For rho=D(a)|0><0|D(a)-adjoint, both sides peak at xi=-a. -/
theorem qFunction_coherent_diagonal {n : ℕ} (hn : 0 < n)
    (rho : State (FockIndex n)) (xi : InterleavedPhaseVector n) :
    qFunction rho.coefficients xi =
      (((2 * Real.pi) ^ n)⁻¹ : ℝ) *
        (conjugateCoefficient (weylCoefficient xi) rho.coefficients
          (fun _ => 0) (fun _ => 0)).re := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
