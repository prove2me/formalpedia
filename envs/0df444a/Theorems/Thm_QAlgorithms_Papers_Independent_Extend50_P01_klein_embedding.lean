-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_klein_embedding
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.klein_embedding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:30:54.09002+00:00
-- url     : https://prove2.me/theorems/a876de35-acb9-48fe-9009-b08dba28cc61
-- title:
--   §II introductory example, Eqs.(10)–(17): Klein-four equivariant embedding
-- statement:
--   For real $x=(x_1,x_2)$, put $E(x)=R_Z(x_1)\otimes R_Z(x_2)$, where $R_Z(t)=e^{-itZ/2}$. Exchange and simultaneous negation act by
--   $$E(x_2,x_1)=\mathrm{SWAP}\,E(x)\,\mathrm{SWAP},\qquad E(-x_1,-x_2)=(X\otimes X)E(x)(X\otimes X).$$
--   The four matrices $I,\mathrm{SWAP},X\otimes X,\mathrm{SWAP}(X\otimes X)$ are unitary and obey the complete Klein-four multiplication law, with exchange/sign bits added modulo two. The embedding is equivariant for every group element. This identifies the full induced symmetry, including its composition law.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 4, §II introductory example, Eqs.(10)–(17): Klein-four equivariant embedding

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

/-- PDF p.4, Eqs.(10)–(17): both identities and the complete group law. -/
theorem klein_embedding :
    kleinMatrix (false, false) = 1 ∧
    (∀ a b, kleinMatrix (kleinMul a b) = kleinMatrix a * kleinMatrix b) ∧
    (∀ a, kleinMatrix a ∈ Matrix.unitaryGroup (Bool × Bool) ℂ) ∧
    (∀ a (x : Fin 2 → ℝ), kleinEncoding (kleinData a x) = conjugate (kleinMatrix a) (kleinEncoding x)) ∧
    (∀ x, kleinEncoding (fun i => x ((Equiv.swap 0 1) i)) = swapGate * kleinEncoding x * swapGate) ∧
    (∀ x, kleinEncoding (-x) = (pauliX ⊗ₖ pauliX) * kleinEncoding x * (pauliX ⊗ₖ pauliX)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
