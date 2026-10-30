-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_exact_spectral_marginal_discrete_seeds
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.exact_spectral_marginal_discrete_seeds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:51:55.297058+00:00
-- url     : https://prove2.me/theorems/66313d44-f23d-45ff-b165-87d7b140c2d0
-- title:
--   Corollary 4.14: exact spectral marginal forces discrete seeds
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   Suppose a covariant permutation-invariant full scheme has the exact marginal $E_N(s^{-1}(B))=\widehat F_N(B)$ for every positive $N$ and Borel spectral event $B$. Then there exist positive operators $Q_{N,Y}$ on the actual Schur factors such that for every Borel state event $A$,
--   $$E_N(A)=\sum_Y\int_{U(d)}\mathbf1_A(U\rho_{Y/N}U^*)\,U^{\otimes N}(Q_{N,Y}\otimes1_{K_Y})(U^*)^{\otimes N}\,dU.$$
--   Each block is embedded through the physical Schur decomposition. The whole family of seeds is chosen from the scheme before the event. This equivalent event form of (124) records the restriction forced by the exact spectral marginal.
--
--   Here $H_Y$ is the actual irreducible unitary Schur factor, $K_Y$ is its Specht multiplicity factor in the physical tensor space, and $Y$ ranges over the diagrams with $N$ boxes and at most $d$ rows.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 24, Corollary 4.14 / (123),(124)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.24, Corollary 4.14, (123)-(124): the actual spectral marginal forces
seeds at Y/N. The witnesses are derived from E; no LDP premise is imposed. -/
theorem exact_spectral_marginal_discrete_seeds {d : ℕ} (hd : 0 < d)
    (E : Scheme d (DensityOutcome d))
    (hcov : ∀ k, CovariantAt (E.observable k))
    (hperm : ∀ k, PermutationInvariantAt (E.observable k))
    (hmarginal : ∀ k B, MeasurableSet B →
      (E.observable k).operator (spectralPreimage B) = spectralEstimatorOperator hd k B) :
    ∃ Q : (k : ℕ) → (Y : Schur.Partition d (k+1)) → Matrix (SchurCoordinateIndex Y) (SchurCoordinateIndex Y) ℂ,
      (∀ k Y, (Q k Y).PosSemidef) ∧
      ∀ k B, MeasurableSet B → (E.observable k).operator B = discreteSeedObservable hd k (Q k) B := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
