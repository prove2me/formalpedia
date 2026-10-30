-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_geometric_ltfim
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.geometric_ltfim
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:50:09.624344+00:00
-- url     : https://prove2.me/theorems/287d74e5-9d27-4f27-8cce-d966f45ac1af
-- title:
--   §V Eqs.(111)–(113): D4-symmetric TTT-LTFIM and shared orbit gates
-- statement:
--   Use the fixed nine-site graph of Fig.12: eight contour edges, four center-to-edge spokes, and four center-to-corner diagonals. For each family $A$, put $H_A=\sum_{(i,j)\in A}Z_iZ_j$. The Hamiltonian
--   $$H=H_{\rm cont}+\tfrac12H_{\rm inside}+\tfrac32H_{\rm diag}+\sum_iX_i+\sum_iZ_i$$
--   is invariant under the board $D_4$ wire action, as is the normalized input $|+\rangle^{\otimes9}$. Twirling each local Pauli generator yields its average over the corresponding vertex orbit, and twirling each edge interaction yields its average over the corresponding edge orbit. Consequently complete shared ZZ/X/Z orbit layers commute with the group. For $p$ layers there are $9p$ named real coordinates, versus $34p$ in the unrestricted per-edge/per-site family. These are syntactic coordinate counts, without independence, minimality, or an X-parity sector claim.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 20, §V Eqs.(111)–(113): D4-symmetric TTT-LTFIM and shared orbit gates

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

/-- PDF pp.19–20, Fig.12 and Eqs.(111)–(113): D4 Hamiltonian and orbit-gate invariance,
with 34p versus 9p syntactic real parameter slots. No parity-sector claim is made. -/
theorem geometric_ltfim (p : ℕ) :
    IsState (plusState 9) ∧
    (∀ s ∈ boardGroup, conjugate (wireMatrix s) latticeHamiltonian = latticeHamiltonian ∧
      act (wireMatrix s) (plusState 9) = plusState 9 ∧
      ∀ theta, Commute (latticeLayer theta) (wireMatrix s)) ∧
    (∀ (a : Fin 3) (i : Fin 9), boardTwirl (onWire i (axis a)) = orbitLocal (axis a) (vertexClass i)) ∧
    (∀ c (e : Fin 9 × Fin 9), e ∈ latticeEdges c →
      boardTwirl (onWire e.1 pauliZ * onWire e.2 pauliZ) = orbitInteraction c) ∧
    Fintype.card (LatticeOriginalParameters p) = 34 * p ∧
    Fintype.card (LatticeSymmetricParameters p) = 9 * p := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
