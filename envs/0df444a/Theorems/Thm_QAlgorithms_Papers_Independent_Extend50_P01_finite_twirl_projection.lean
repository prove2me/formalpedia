-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_finite_twirl_projection
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.finite_twirl_projection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:38:48.530091+00:00
-- url     : https://prove2.me/theorems/3c3c91bc-c570-4d91-89dc-d93f3a83992d
-- title:
--   Proposition 2 (Twirling formula [41])
-- statement:
--   Let $S$ be a finite group with unitary representation $U$ on $n$ qubits. For every complex operator $X$, define $T(X)=|S|^{-1}\sum_sU_sXU_s^\dagger$. This map is complex-linear and satisfies
--   $$T^2=T,\qquad\operatorname{range}T=\{X:[X,U_s]=0\text{ for every }s\},\qquad T(X)=X\iff\forall s,\ [X,U_s]=0.$$
--   In particular $T(X)$ always commutes with every represented symmetry. These conclusions specify a projection onto the whole commutant, including the pointwise fixed property, for arbitrary operators rather than only Hermitian inputs.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 8, Proposition 2 (Twirling formula [41])

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

/-- PDF p.8, Proposition 2: complex-linear idempotent with exact range and fixed points. -/
theorem finite_twirl_projection {S : Type*} [Group S] [Fintype S]
    (n : ℕ) (U : S →* Op n) (hU : ∀ s, U s ∈ Matrix.unitaryGroup (Qubits n) ℂ) :
    (∀ X Y, finiteTwirl U (X + Y) = finiteTwirl U X + finiteTwirl U Y) ∧
    (∀ (c : ℂ) X, finiteTwirl U (c • X) = c • finiteTwirl U X) ∧
    (∀ X, finiteTwirl U (finiteTwirl U X) = finiteTwirl U X) ∧
    Set.range (finiteTwirl U) = {X | ∀ s, Commute X (U s)} ∧
    (∀ X, finiteTwirl U X = X ↔ ∀ s, Commute X (U s)) ∧
    (∀ X s, Commute (finiteTwirl U X) (U s)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
