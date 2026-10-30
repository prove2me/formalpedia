-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_u1_covariance
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.u1_covariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:21:20.214021+00:00
-- url     : https://prove2.me/theorems/c150a690-bf92-43c1-beb9-7b1dd75f28d1
-- title:
--   Proposition 1: U(1) covariance
-- statement:
--   Let $n,k,t,\alpha$ be integers with $0\le k,t\le n$ and $0\le\alpha\le n-k$. Append a fixed unit vector of charge $\alpha$ to $k$ logical qubits and conjugate by a Haar-random unitary in the full commutant of the $n$-qubit Hamming-weight operator. Erase a fixed known set of $t$ sites. Let $\epsilon_{\rm Choi}$ and $\epsilon_{\rm worst}$ denote the optimal CPTP recovery errors, using root fidelity $F$ and purified distance $P=\sqrt{1-F^2}$, respectively on the normalized maximally entangled input and on all reference-entangled inputs with one common decoder.
--
--   For every allowed fixed encoding unitary and every logical density matrix $\rho$ and real $\theta$, the encoding channel $\mathcal E$ satisfies
--   $$\mathcal E(e^{-i\theta Q(k)}\rho e^{i\theta Q(k)})=e^{-i\theta Q(n)}\mathcal E(\rho)e^{i\theta Q(n)}.$$
--
--   The charge-$\alpha$ phase cancels at channel level, so no zero-charge condition is needed.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 5, Proposition 1: U(1) covariance

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- Proposition 1, PDF p.5. Ancillary charge contributes only a cancelling
channel-level phase; alpha need not be zero. -/
theorem u1_covariance (n k alpha : ℕ) (hk : k ≤ n) (ha : alpha ≤ n-k)
    (psi : EuclideanSpace ℂ (CovariantWord 2 (n-k))) (hpsi : ChargeState alpha psi)
    (U : Op (CovariantWord 2 n)) (hU : U1Group n U) (theta : ℝ)
    (rho : Op (CovariantWord 2 k)) (hrho : IsDensityMatrix rho) :
    appendUnitaryEncoder hk (pureDensity psi) U
      (chargeRotation k theta * rho * (chargeRotation k theta)ᴴ) =
    chargeRotation n theta * appendUnitaryEncoder hk (pureDensity psi) U rho * (chargeRotation n theta)ᴴ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
