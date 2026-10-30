-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_full_estimator_structure
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.full_estimator_structure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:38:21.014072+00:00
-- url     : https://prove2.me/theorems/39626226-8dca-4573-9a4c-dddd1b0f35cb
-- title:
--   Unnumbered main properties (22): marginal, covariance and permutation invariance
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   Let $\widehat E_N$ be the explicit highest-weight estimator (20), let $\widehat F_N$ be (17), and let $s$ be the ordered-spectrum map. For every positive $N$,
--   $$\widehat E_N(s^{-1}(B))=\widehat F_N(B),\qquad \widehat E_N(UBU^*)=U^{\otimes N}\widehat E_N(B)(U^*)^{\otimes N},\qquad V_\pi\widehat E_N(B)V_\pi^*=\widehat E_N(B).$$
--   The first identity holds for Borel $B\subseteq\Sigma$, and the last two for Borel state events, every unitary $U$, and every tensor-factor permutation $\pi$, whose action uses $\pi^{-1}$. These are exact finite-copy structural properties and require no LDP premise.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 7, Main properties / (22)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.7-8, (22): exact spectral marginal, covariance, and permutation
invariance of the concrete full estimator, for every positive copy count. -/
theorem full_estimator_structure {d : ℕ} (hd : 0 < d) (k : ℕ) :
    (∀ B : Set (OrderedSpectrum d), MeasurableSet B →
      fullEstimatorOperator hd k (spectralPreimage B) = spectralEstimatorOperator hd k B) ∧
    (∀ (U : Matrix.unitaryGroup (Fin d) ℂ) B, MeasurableSet B →
      fullEstimatorOperator hd k (conjugateState U '' B) =
        piKron (k+1) (U : Matrix (Fin d) (Fin d) ℂ) * fullEstimatorOperator hd k B * star (piKron (k+1) (U : Matrix (Fin d) (Fin d) ℂ))) ∧
    (∀ (p : Equiv.Perm (Fin (k+1))) B, MeasurableSet B →
      Schur.tensorPermutation d (k+1) p * fullEstimatorOperator hd k B *
        star (Schur.tensorPermutation d (k+1) p) = fullEstimatorOperator hd k B) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
