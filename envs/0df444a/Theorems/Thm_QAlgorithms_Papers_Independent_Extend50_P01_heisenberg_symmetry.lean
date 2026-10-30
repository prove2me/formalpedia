-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_heisenberg_symmetry
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.heisenberg_symmetry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:47:53.311951+00:00
-- url     : https://prove2.me/theorems/a26497eb-ffce-4fb3-a782-3ba29c6f3cc5
-- title:
--   §V Eqs.(99)–(101): Heisenberg symmetry and singlet-product initialization
-- statement:
--   For a periodic chain of $N=2k$ spins, $k\ge1$, let $H=\sum_i(X_iX_{i+1}+Y_iY_{i+1}+Z_iZ_{i+1})$. For $V\in SU(2)$ define $U_V=V^{\otimes N}$. These matrices are unitary and obey the representation law, and $[H,U_V]=0$. The neighboring-singlet product $\psi_0=\bigotimes_{j=1}^k(|01\rangle-|10\rangle)/\sqrt2$ satisfies
--   $$\|\psi_0\|=1,\qquad U_V\psi_0=\psi_0\quad(V\in SU(2)),\qquad J^2\psi_0=0,$$
--   where $J^2=\sum_{a=X,Y,Z}(\frac12\sum_i a_i)^2$. This supplies an invariant zero-total-spin initialization, without asserting that the singlet product itself is a ground state. The Hamiltonian is Hermitian and has a normalized ground state, and every normalized ground state psi satisfies J^2 psi = 0. This is the ground-sector assertion on pp.17–18; it does not identify the chosen singlet product with a ground state.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 17, §V Eqs.(99)–(101): Heisenberg symmetry and singlet-product initialization

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P01

noncomputable section

open scoped Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P01

attribute [local instance] Classical.propDecidable Classical.decEq

-- PDF pp.3,8: reuse the accepted operator type, exp(-itH), and A X A†.
-- Notation specializes the imported interfaces without introducing duplicate declarations.

local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "evolve" => QAlgorithms.Papers.Independent.Information100.P32.evolution

local notation "conjugate" => QAlgorithms.conjSuperop

-- PDF pp.3,10–11: the imported quadratic form is Re(psi† A psi).

local notation "expectation" => QAlgorithms.Papers.Independent.Information100.P21.quad

-- PDF pp.5,16–19: accepted active-wire operator, with identities on all spectators.

local notation "onWire" => QAlgorithms.Papers.Independent.Advance50.P49.onWire

-- PDF p.5: the imported phase-free Pauli tensor uses 0=I,1=X,2=Y,3=Z.

local notation "pauliWord" => QAlgorithms.Papers.Independent.Gap48.P33.pauliWord

local notation "parity" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P69.matrixPower pauliX n)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P01.su2MeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P01.su2BorelSpace

local notation "collective" => (fun (n : ℕ) (V : SU2) => QAlgorithms.Papers.Independent.Information100.P69.matrixPower (Subtype.val V) n)

/-- PDF pp.17–18, Eqs.(99)–(101): Hamiltonian symmetry, zero-spin ground sector,
and invariant singlet-product input. Every normalized ground state has total spin zero;
the chosen singlet product is only asserted to be an initial state in that sector. -/
theorem heisenberg_symmetry (k : ℕ) (hk : 1 ≤ k) :
    collective (2 * k) (1 : SU2) = 1 ∧
    (∀ V W : SU2, collective (2 * k) (V * W) = collective (2 * k) V * collective (2 * k) W) ∧
    (∀ V : SU2, Commute (heisenberg (2 * k)) (collective (2 * k) V)) ∧
    (∀ V : SU2, collective (2 * k) V ∈ Matrix.unitaryGroup (Qubits (2 * k)) ℂ ∧
      act (collective (2 * k) V) (singletProduct k) = singletProduct k) ∧
    IsState (singletProduct k) ∧ act (totalSpinSquared (2 * k)) (singletProduct k) = 0 ∧
    (heisenberg (2 * k)).IsHermitian ∧
    (∃ psi, IsGroundState (heisenberg (2 * k)) psi) ∧
    (∀ psi, IsGroundState (heisenberg (2 * k)) psi →
      act (totalSpinSquared (2 * k)) psi = 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
