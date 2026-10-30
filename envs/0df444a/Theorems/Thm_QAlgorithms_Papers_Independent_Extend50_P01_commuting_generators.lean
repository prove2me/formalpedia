-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_commuting_generators
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.commuting_generators
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:38:00.515471+00:00
-- url     : https://prove2.me/theorems/9e164ccc-8cce-464a-87dd-4d0757a1d31a
-- title:
--   Proposition 1 (Commuting generators)
-- statement:
--   Let $U:S\to U(2^n)$ be a unitary representation of a group, and let $G$ be Hermitian. Then
--   $$\bigl(\forall\theta\in\mathbb R\ \forall s\in S,\ [e^{-i\theta G},U_s]=0\bigr)\quad\Longleftrightarrow\quad\bigl(\forall s\in S,\ [G,U_s]=0\bigr).$$
--   The equivalence concerns all real angles, rather than a single selected gate angle. It transfers gate equivariance to a condition on the generator.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 8, Proposition 1 (Commuting generators)

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

/-- PDF p.8, Proposition 1: universal angle and symmetry quantifiers on the left of iff. -/
theorem commuting_generators {S : Type*} [Group S] (n : ℕ) (U : S →* Op n)
    (hU : ∀ s, U s ∈ Matrix.unitaryGroup (Qubits n) ℂ) (G : Op n) (hG : G.IsHermitian) :
    (∀ (theta : ℝ) (s : S), Commute (evolve G theta) (U s)) ↔ ∀ s, Commute G (U s) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
