-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P85_quadrature_correlation_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P85.quadrature_correlation_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:15:28.612704+00:00
-- url     : https://prove2.me/theorems/ed301b03-0cf9-43e9-8f63-6482da5846bb
-- title:
--   p.2: quantum and proper-P classical correlation limits
-- statement:
--   Fix $N_S\ge0$ and the source quadrature normalization with vacuum covariance $I/4$. Let $\rho$ be any centered, normalized two-mode density with finite second moments and covariance
--   $$
--   \Lambda(C)=\frac14\begin{pmatrix}S&0&C&0\\0&S&0&-C\\C&0&S&0\\0&-C&0&S\end{pmatrix},\qquad S=2N_S+1.
--   $$
--   Then
--   $$
--   |C|\le C_q=2\sqrt{N_S(N_S+1)},\qquad
--   \rho\text{ has a positive P representation}\ \Longrightarrow\ |C|\le C_c=2N_S.
--   $$
--   The constructed SPDC state attains $C_q$, and some positive-P state attains $C_c$. Positive P means an integrable coherent-projector barycenter under a Borel probability measure, which may be singular. Moreover $C_q/C_c\to+\infty$ as $N_S\to0^+$. These are sharp quadrature-correlation limits; no claim about maximal entanglement entropy is made.
-- source:
--   Quantum Illumination with Gaussian States, arXiv:0810.0534v1, PDF p. 2, p.2: quantum and proper-P classical correlation limits

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P85

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P85

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Renew46.P41 (coherentProductCoefficient)

/-- Source p.2 after (2): sharp quantum and positive-P classical limits
for the phase-sensitive covariance family with the source's fixed diagonal.
Maximal quadrature correlation is not maximal infinite-dimensional entropy. -/
theorem quadrature_correlation_bounds (NS : ℝ) (hNS : 0 ≤ NS)
    (W : G.FockWeylSystem 2) :
    (∀ (X : Array (Occ 2)) (C : ℝ),
      CenteredMoments W X (phaseSensitiveWignerCov (signalS NS) (signalS NS) C) →
      |C| ≤ correlationQ NS ∧ (PositiveP X → |C| ≤ correlationC NS)) ∧
    CenteredMoments W (spdcArray NS) (spdcCov NS) ∧
    (∃ X : Array (Occ 2), PositiveP X ∧
      CenteredMoments W X (phaseSensitiveWignerCov (signalS NS) (signalS NS) (correlationC NS))) ∧
    Tendsto (fun x : ℝ => correlationQ x / correlationC x)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P85

end
