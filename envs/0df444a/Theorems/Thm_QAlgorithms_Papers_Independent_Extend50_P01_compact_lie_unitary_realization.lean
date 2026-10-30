-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_compact_lie_unitary_realization
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.compact_lie_unitary_realization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:51:10.656778+00:00
-- url     : https://prove2.me/theorems/4f3a621b-f747-48b4-90f0-39ec994e432a
-- title:
--   Compact Lie symmetries admit faithful quantum unitary representations
-- statement:
--   For every compact real Lie group S of finite real dimension d, with its Hausdorff second-countable manifold topology, there exist a nonnegative integer n and a continuous injective group homomorphism U from S to SU(2^n), acting on the fixed n-qubit computational basis. Compactness is retained throughout the source sentence.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 6, §II Continuous symmetries: compact unitary realization

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

/-- PDF p.6, continuous symmetries: a compact real Lie group has a faithful quantum
unitary realization. SOURCE CORRECTION: the printed follow-up says "every Lie group";
retain "compact" from the preceding sentence, since an arbitrary noncompact Lie group
need not have a faithful finite-dimensional unitary representation. -/
theorem compact_lie_unitary_realization (d : ℕ) {S : Type*} [Group S] [TopologicalSpace S]
    [IsTopologicalGroup S] [CompactSpace S] [T2Space S] [SecondCountableTopology S]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) S]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) ∞ S]
    [LieGroup (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) ∞ S] :
    ∃ (n : ℕ) (U : S →* Matrix.specialUnitaryGroup (Qubits n) ℂ),
      Continuous U ∧ Function.Injective U := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
