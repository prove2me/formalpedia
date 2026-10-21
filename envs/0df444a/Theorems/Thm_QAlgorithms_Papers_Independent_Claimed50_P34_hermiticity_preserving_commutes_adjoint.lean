-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P34_hermiticity_preserving_commutes_adjoint
-- name    : QAlgorithms.Papers.Independent.Claimed50.P34.hermiticity_preserving_commutes_adjoint
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:51:55.2054+00:00
-- url     : https://prove2.me/theorems/723106f0-71bb-4c0a-9af3-891cac67bfd4
-- title:
--   Hermiticity-preserving linear maps commute with adjoints on adjoint-stable subspaces
-- statement:
--   Let $H_1,H_2$ be complete separable complex Hilbert spaces, and write $\mathcal L(H_i)$ for their bounded complex-linear endomorphisms. Let $V\subseteq\mathcal L(H_2)$ be a complex-linear subspace invariant under taking adjoints. Let $\Phi:V\to\mathcal L(H_1)$ be a complex-linear map such that $\Phi(A)$ is self-adjoint whenever $A\in V$ is self-adjoint. Then
--
--   $$
--   \Phi(A^\dagger)=\Phi(A)^\dagger\qquad\text{for every }A\in V.
--   $$
--
--   The subspace need not be topologically closed, and no continuity assumption on $\Phi$ is required. This establishes adjoint compatibility on the full domain of a Hermiticity-preserving map.
-- source:
--   On the relation between states and maps in infinite dimensions, arXiv:0706.2617v1, PDF p. 13, Proposition 3; setup on p.12

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P34

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P34

/-- PDF p.13, Proposition 3 (setup on p.12): a complex-linear map on any
adjoint-stable linear subspace of bounded operators that preserves Hermiticity
commutes with the adjoint. Stability means algebraic closure under adjoints,
not topological closedness. No continuity of Phi is assumed.
The subtype in the conclusion uses only the given adjoint-stability hypothesis. -/
theorem hermiticity_preserving_commutes_adjoint
    {H1 H2 : Type*}
    [NormedAddCommGroup H1] [InnerProductSpace ℂ H1] [CompleteSpace H1]
    [TopologicalSpace.SeparableSpace H1]
    [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] [CompleteSpace H2]
    [TopologicalSpace.SeparableSpace H2]
    (V : Submodule ℂ (H2 →L[ℂ] H2))
    (adjointStable : ∀ A : V, A.val.adjoint ∈ V)
    (Phi : V →ₗ[ℂ] (H1 →L[ℂ] H1))
    (preservesHermiticity : ∀ A : V, A.val.adjoint = A.val →
      (Phi A).adjoint = Phi A) :
    ∀ A : V, Phi ⟨A.val.adjoint, adjointStable A⟩ = (Phi A).adjoint := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P34

end
