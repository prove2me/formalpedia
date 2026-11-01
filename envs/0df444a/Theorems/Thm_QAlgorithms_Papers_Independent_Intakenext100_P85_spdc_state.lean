-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P85_spdc_state
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P85.spdc_state
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:14:31.477583+00:00
-- url     : https://prove2.me/theorems/cb7aff47-c46b-409a-bbc9-4ed92a0e691a
-- title:
--   Eqs.(1)–(2): SPDC number state and Wigner covariance
-- statement:
--   Let $N_S\ge0$. On the complete two-mode oscillator space, define
--   $$
--   |\psi_{N_S}\rangle=\sum_{n=0}^{\infty}\sqrt{\frac{N_S^n}{(N_S+1)^{n+1}}}|n,n\rangle.
--   $$
--   This vector has norm one, and each marginal has finite mean photon number $N_S$. Its pure density is a zero-mean Gaussian state. With interleaved quadratures $(q_S,p_S,q_I,p_I)$, $q=(a+a^\dagger)/2$, $p=(a-a^\dagger)/(2i)$, its covariance is
--   $$
--   \Lambda_{SI}=\frac14\begin{pmatrix}S&0&C_q&0\\0&S&0&-C_q\\C_q&0&S&0\\0&-C_q&0&S\end{pmatrix},\qquad S=2N_S+1,\quad C_q=2\sqrt{N_S(N_S+1)}.
--   $$
--   For $N_S>0$ the signal and idler are entangled; at $N_S=0$ the state is the two-mode vacuum. This identifies the actual illumination resource and its normalization.
-- source:
--   Quantum Illumination with Gaussian States, arXiv:0810.0534v1, PDF p. 2, Eqs.(1)–(2): SPDC number state and Wigner covariance

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P85

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P85

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Renew46.P41 (coherentProductCoefficient)

/-- Source p.2, Eqs.(1)–(2). The constructed number vector is normalized,
has marginal energy NS and the displayed zero-mean Gaussian covariance.
Only NS>0 implies entanglement; NS=0 is retained as vacuum. -/
theorem spdc_state (NS : ℝ) (hNS : 0 ≤ NS) (W : G.FockWeylSystem 2) :
    (∀ j, spdcVector NS j = spdcCoefficient NS j) ∧
    ‖spdcVector NS‖ = 1 ∧ T.IsDensity (spdcArray NS) ∧
    SourceGaussian W (spdcArray NS) 0 (spdcCov NS) ∧
    (∀ k : Fin 2, Summable (fun j : Occ 2 => (j k : ℝ) * (spdcArray NS j j).re) ∧
      marginalPhotonNumber (spdcArray NS) k = NS) ∧
    (0 < NS → ¬ T.IsSeparable (pairArray (spdcArray NS))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P85

end
