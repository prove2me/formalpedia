-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_tfim_symmetry
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.tfim_symmetry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:46:06.896715+00:00
-- url     : https://prove2.me/theorems/0a526851-a4d9-4cee-b5a9-5bd4cb1a6b8d
-- title:
--   §V Eqs.(94)–(96): TFIM parity and ground-state sector
-- statement:
--   For a periodic chain of $N\ge1$ qubits and real $g>0$, let $H=-\sum_iZ_iZ_{i+1}-g\sum_iX_i$, with cyclic successor, and $P=\bigotimes_iX_i$. Then $[H,P]=0$, $P^2=I$, and the ground level of $H$ is simple and attained. Every normalized ground state has positive parity:
--   $$H\psi=E_{\min}\psi,\quad\|\psi\|=1\quad\Longrightarrow\quad P\psi=\psi.$$
--   The state $|+\rangle^{\otimes N}$ is normalized; any finite circuit of parity-commuting unitaries preserves its positive-parity sector. At $N=1$ the literal periodic interaction is $Z_1^2=I$. This identifies the sector relevant to the source's ansatz construction without assuming the source's nondegeneracy conclusion.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 16, §V Eqs.(94)–(96): TFIM parity and ground-state sector

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

/-- PDF pp.16–17, Eqs.(94)–(96): positive-field TFIM has a simple even-parity ground level.
Nondegeneracy is a conclusion, not a hypothesis. -/
theorem tfim_symmetry (N : ℕ) (hN : 1 ≤ N) (g : ℝ) (hg : 0 < g) :
    Commute (tfim N g) (parity N) ∧ parity N ^ 2 = 1 ∧
    IsState (plusState N) ∧ HasSimpleGroundState (tfim N g) ∧
    (∃ psi, IsGroundState (tfim N g) psi) ∧
    (∀ psi, IsGroundState (tfim N g) psi → act (parity N) psi = psi) ∧
    (∀ k (W : Fin k → Op N), (∀ j, W j ∈ Matrix.unitaryGroup (Qubits N) ℂ) →
      (∀ j, Commute (W j) (parity N)) →
      act (parity N) (act (orderedProd W) (plusState N)) = act (orderedProd W) (plusState N)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
