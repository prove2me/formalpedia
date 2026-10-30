-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P41_covariant_observable_structure
-- name    : QAlgorithms.Papers.Independent.Extend50.P41.covariant_observable_structure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:50:27.192051+00:00
-- url     : https://prove2.me/theorems/d6fbb964-78a2-4176-af8b-5eb689b0d744
-- title:
--   Theorem 4.12: general covariant permutation-invariant observable structure
-- statement:
--   Let $d\ge1$, let $\mathcal S$ be the positive semidefinite trace-one matrices on $\mathbb C^d$, including singular matrices, and give $\mathcal S$ its usual matrix topology and Borel sets. Copy counts are positive. A scheme consists of normalized countably additive positive operator measures $E_N$ on $(\mathbb C^d)^{\otimes N}$, fixed independently of the unknown input. Its Born law is $\mu_{N,\rho}(B)=\operatorname{Tr}(\rho^{\otimes N}E_N(B))$. All logarithms are natural.
--
--   Fix positive $N$ and a normalized full-state observable $E$ that is covariant and permutation invariant. In the actual Schur decomposition there exist finite positive operator measures $q_Y$ on $\Sigma$, acting on $H_Y$, such that for every Borel state event $B$,
--   $$E(B)=\bigoplus_Y\left[\int_{U(d)}\pi_Y(U)\,q_Y\bigl(\{x:U\rho_xU^*\in B\}\bigr)\,\pi_Y(U)^*\,dU\right]\otimes1_{K_Y}.$$
--   Here $\rho_x=\operatorname{diag}x$, and Haar measure is normalized. The seeds need not obey $q_Y(\Sigma)=1$. This Borel-event identity is equivalent to (108) for all continuous real test functions and describes every such finite-copy observable.
--
--   Here $H_Y$ is the actual irreducible unitary Schur factor, $K_Y$ is its Specht multiplicity factor in the physical tensor space, and $Y$ ranges over the diagrams with $N$ boxes and at most $d$ rows. The notation $\pi_Y$ denotes the unitary action restricted to $H_Y$.
-- source:
--   Quantum state estimation and large deviations, arXiv:quant-ph/0412053v2, PDF p. 21, Theorem 4.12 / (108)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P41

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexOrder ENNReal Topology Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Extend50.P41

open QAlgorithms.Tomography (DensityOutcome)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.21-23, Theorem 4.12, (108), in equivalent Borel-event form.
The physical decomposition is computed, not assumed as a block certificate.
The seeds are finite positive operator measures and need not be normalized. -/
theorem covariant_observable_structure {d : ℕ} (hd : 0 < d) (k : ℕ)
    (E : Measurements.OperatorPOVM (CopyIndex d k) (DensityOutcome d))
    (hcov : CovariantAt E) (hperm : PermutationInvariantAt E) :
    ∃ q : (Y : Schur.Partition d (k+1)) → FiniteOperatorMeasure (SchurCoordinateIndex Y) (OrderedSpectrum d),
      ∀ B : Set (DensityOutcome d), MeasurableSet B →
        E.operator B = ∑ Y : Schur.Partition d (k+1), embedBlock Y (seedObservable Y (q Y) B) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P41

end
