-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_full_estimator_LDP
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.full_estimator_LDP
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:36:06.920784+00:00
-- url     : https://prove2.me/theorems/982466d4-8a13-4bc3-9654-d175f411fc75
-- title:
--   Theorem 3.2 / abstract: full density-matrix estimator, consistency and explicit LDP
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   For a Young shape $Y$ with $N$ boxes and at most $d$ rows, let $H_Y,K_Y$ be the actual Schur and Specht factors and let $\phi_Y$ be the normalized highest-weight vector of the representation $\pi_Y$. With probability Haar measure $dU$, the explicit observable is
--   $$\widehat E_N(B)=\sum_Y\dim H_Y\int_{U(d)}\mathbf1_B(U\rho_{Y/N}U^*)\,|\pi_Y(U)\phi_Y\rangle\langle\pi_Y(U)\phi_Y|\otimes1_{K_Y}\,dU.$$
--   It is a normalized full-estimation scheme, is weakly consistent, and satisfies the LDP with
--   $$\widehat I(\rho,U\rho_xU^*)=\sum_{j=1}^d x_j\log x_j-\sum_{j=1}^d(x_j-x_{j+1})\log\operatorname{pm}_j(U^*\rho U).$$
--   Here $x$ belongs to the ordered probability simplex $\Sigma$, $x_{d+1}=0$, $\rho_x=\operatorname{diag}x$, and $\operatorname{pm}_j$ is the leading $j$-dimensional principal determinant. A zero coefficient times a vanishing logarithm contributes zero, and a positive coefficient at a zero minor contributes infinity. The rate is independent of the diagonalization. Thus this is a concrete consistent full-state estimator with an explicit error exponent.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 8, Theorem 3.2 / (20),(26)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Theorem 3.2, (26), with the explicit observable (20) on p.7.
Singular inputs are included. A normalized POVM witness for the raw expression
is asserted, and is fixed independently of the unknown input. -/
theorem full_estimator_LDP {d : ℕ} (hd : 0 < d) :
    ∃ E : Scheme d (DensityOutcome d),
      (∀ k B, MeasurableSet B → (E.observable k).operator B = fullEstimatorOperator hd k B) ∧
      SchemeLDP E FullTarget fullRate ∧ Consistent E ∧
      ∀ (rho sigma : DensityOutcome d) (x : OrderedSpectrum d) (U : Matrix.unitaryGroup (Fin d) ℂ),
        sigma.val = (U : Matrix (Fin d) (Fin d) ℂ) * diagonalStateMatrix x * star (U : Matrix (Fin d) (Fin d) ℂ) →
        (fullRate rho sigma : EReal) = minorFormula rho U x := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
