-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_haar_twirl_projection
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.haar_twirl_projection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:39:56.029347+00:00
-- url     : https://prove2.me/theorems/e0353694-0dc3-46a6-bfe2-a31ab16c8830
-- title:
--   §III Eq.(53): compact continuous-group twirling projection
-- statement:
--   Let $S$ be a compact real Lie group of arbitrary finite dimension, with its Hausdorff second-countable manifold topology, equipped with a normalized probability Haar measure $\mu$, and let $U$ be a continuous finite-dimensional unitary representation on $n$ qubits. Then the conjugation integrand is integrable for every $X$, and
--   $$T(X)=\int_SU_sXU_s^\dagger\,d\mu(s)$$
--   is complex-linear, idempotent, has range precisely the commutant, and fixes an operator exactly when that operator commutes with every $U_s$. Hermitian inputs remain Hermitian. This is the compact normalized averaging interpretation of the source's Lie-group extension; the Lean quantifiers retain the source's Lie-group domain.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 8, §III Eq.(53): compact continuous-group twirling projection

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

/-- PDF p.8, Eq.(53): normalized compact real Lie-group averaging.
Continuity gives integrability; d is the real manifold dimension of the symmetry group. -/
theorem haar_twirl_projection (d : ℕ) {S : Type*} [Group S] [TopologicalSpace S]
    [IsTopologicalGroup S] [CompactSpace S] [T2Space S] [SecondCountableTopology S]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) S]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) ∞ S]
    [LieGroup (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) ∞ S]
    [MeasurableSpace S] [BorelSpace S]
    (mu : Measure S) [Measure.IsHaarMeasure mu] [IsProbabilityMeasure mu]
    (n : ℕ) (U : S →* Op n) (hU : ∀ s, U s ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hcont : Continuous U) :
    (∀ X, Integrable (fun s => conjugate (U s) X) mu) ∧
    (∀ X Y, operatorHaarAverage mu U (X + Y) = operatorHaarAverage mu U X + operatorHaarAverage mu U Y) ∧
    (∀ (c : ℂ) X, operatorHaarAverage mu U (c • X) = c • operatorHaarAverage mu U X) ∧
    (∀ X, operatorHaarAverage mu U (operatorHaarAverage mu U X) = operatorHaarAverage mu U X) ∧
    Set.range (operatorHaarAverage mu U) = {X | ∀ s, Commute X (U s)} ∧
    (∀ X, operatorHaarAverage mu U X = X ↔ ∀ s, Commute X (U s)) ∧
    (∀ X, X.IsHermitian → (operatorHaarAverage mu U X).IsHermitian) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
