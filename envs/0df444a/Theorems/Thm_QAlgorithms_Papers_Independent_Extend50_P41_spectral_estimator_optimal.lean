-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_spectral_estimator_optimal
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.spectral_estimator_optimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:36:56.249307+00:00
-- url     : https://prove2.me/theorems/54fdd586-aa44-4b91-84ea-62268d66c6b0
-- title:
--   Theorem 3.1: strongly asymptotically optimal spectral estimation
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   Let $s(\rho)$ be the eigenvalues in decreasing order, and let $P_Y$ be the physical projector onto $H_Y\otimes K_Y$. The explicit spectral observable $\widehat F_N(B)=\sum_{Y/N\in B}P_Y$ is normalized and attains every spectral optimum:
--   $$I_s(\rho,x)=I_s^0(\rho,x)=I_s^c(\rho,x)=\sum_{j=1}^d x_j\bigl(\log x_j-\log s_j(\rho)\bigr).$$
--   The sum uses the classical support conventions. The three optima take suprema over all spectral rates, jointly lower semicontinuous spectral rates, and rates with a covariant spectral witness, respectively. The Born laws of $\widehat F_N$ satisfy the LDP with this rate. This is strong asymptotic optimality for estimating the spectrum.
--
--   Here $H_Y$ is the actual irreducible unitary Schur factor, $K_Y$ is its Specht multiplicity factor in the physical tensor space, and $Y$ ranges over the diagrams with $N$ boxes and at most $d$ rows.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 7, Theorem 3.1 / (17),(19)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, Theorem 3.1: the explicit spectral observable (17) has the optimal
rate (19); unrestricted, jointly lower semicontinuous and covariant optima agree. -/
theorem spectral_estimator_optimal {d : ℕ} (hd : 0 < d) :
    ∃ F : Scheme d (OrderedSpectrum d),
      (∀ k B, MeasurableSet B → (F.observable k).operator B = spectralEstimatorOperator hd k B) ∧
      SchemeLDP F SpectralTarget spectralRate ∧
      ∀ (rho : DensityOutcome d) (x : OrderedSpectrum d), optimalRate SpectralTarget false rho x = spectralRate rho x ∧
        optimalRate SpectralTarget true rho x = spectralRate rho x ∧
        spectralCovariantOptimal rho x = spectralRate rho x := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
