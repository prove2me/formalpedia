-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_su_covariance
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.su_covariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:27:28.603169+00:00
-- url     : https://prove2.me/theorems/839cdd1a-8ae9-4b9b-bc35-53f19c12fa0b
-- title:
--   Proposition 4: SU(d) covariance
-- statement:
--   Fix an integer $d\ge2$. For $n\ge2$ let $\lambda$ partition $n-1$ with at most $d$ rows, and let $l_\lambda,r_\lambda$ be the actual Schur and Specht module dimensions. Append the physical isotypic embedding of $I_{L_\lambda}/l_\lambda\otimes|\psi_\lambda\rangle\langle\psi_\lambda|$, where $\psi_\lambda$ is a fixed unit Specht vector, to one logical $d$-level system. Conjugate by Haar measure on the determinant-one commutant of the collective $SU(d)$ action and erase one fixed known site. Errors mean optimal CPTP recovery measured in root-fidelity purified distance, with normalized Choi input and a decoder chosen before the worst reference-entangled input.
--
--   For every allowed fixed encoding unitary, every $U\in SU(d)$, and every logical density matrix $\rho$,
--   $$\mathcal E(U\rho U^\dagger)=U^{\otimes n}\mathcal E(\rho)(U^\dagger)^{\otimes n}.$$
--
--   The maximally mixed Schur factor in the actual ancilla is essential to this channel covariance statement.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 11, Proposition 4: SU(d) covariance

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

/-- Proposition 4, PDF p.11. Actual embedded I_L/l tensor pure Specht
ancilla; covariance concerns channels and permits a mixed ancilla. -/
theorem su_covariance (d n : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n)
    (lam : Schur.Partition d (n-1))
    (psi : EuclideanSpace ℂ (Fin (rdim lam))) (hpsi : IsState psi)
    (V : Op (CovariantWord d n)) (hV : SUGroup d n V)
    (U : Op (Fin d)) (hU : Uᴴ * U = 1) (hdet : U.det = 1)
    (rho : Op (CovariantWord d 1)) (hrho : IsDensityMatrix rho) :
    appendUnitaryEncoder (show 1 ≤ n by omega) (suAncilla lam psi) V
      (collectiveQuditAction 1 U * rho * (collectiveQuditAction 1 U)ᴴ) =
    collectiveQuditAction n U * appendUnitaryEncoder (show 1 ≤ n by omega) (suAncilla lam psi) V rho *
      (collectiveQuditAction n U)ᴴ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
