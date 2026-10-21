-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_coherenceIndex_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P31.coherenceIndex_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:25:15.671625+00:00
-- url     : https://prove2.me/theorems/58cbfc89-22c1-40d4-bfb9-0925d940c4b3
-- title:
--   Proposition 2.2: elementary coherence-index properties
-- statement:
--   Let $H$ be any complex Hilbert space, let $\rho$ be a positive trace-class operator of trace one, and let $(A_j)_{j=1}^d$ be a finite family of densely defined self-adjoint operators such that every $A_j\rho$ has a trace-class bounded realization. Write $C_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|[A_j,\rho]\|_2^2)^{1/2}$ and $D_A(\rho)=\|\rho\|_2^{-1}(\sum_j\|\{A_j-\operatorname{Tr}(A_j\rho),\rho\}\|_2^2)^{1/2}$, where $\|\cdot\|_2$ denotes Hilbert–Schmidt norm, and put $S_A=C_A/D_A$. Assume $D_A(\rho)\ne0$. Then
--
--   $$
--   0\le S_A(\rho)\le1,\qquad S_A(\rho)=0\iff [A_j,\rho]=0\text{ for every }j.
--   $$
--
--   If $\rho=|f\rangle\langle f|$ is pure, with $\|f\|=1$, then $S_A(\rho)=1$. The nonzero-spread domain excludes simultaneous eigenvectors in this last clause.
--
--   These facts give the basic interpretation and normalization of the general observable coherence index.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 9, Proposition 2.2: elementary coherence-index properties

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P31

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Next46.P31

open QAlgorithms.PeriodicSchrodinger (Position)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace)

section ObservableCoherence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Clark, PDF pp.8–9, Proposition 2.2, all three clauses. The nonzero spread
is inherited from Definition 2.1; for a pure state it excludes simultaneous
eigenvectors, exactly as required by the source's domain. -/
theorem coherenceIndex_properties {I : Type*} {d : ℕ} (b : HilbertBasis I ℂ H)
    (A : Fin d →
      QAlgorithms.Papers.Independent.Frontier30.P22.SelfAdjointHamiltonian (H := H))
    (rho : H →L[ℂ] H) (hrho : IsTraceClass rho ∧ IsPositive rho ∧ operatorTrace b rho = 1)
    (hregular : ∀ j, RegularProduct (observableGraph (A j)) rho)
    (hspread : coherenceSpread b (fun j => observableGraph (A j)) rho ≠ 0) :
    coherenceIndex b (fun j => observableGraph (A j)) rho ∈ Set.Icc (0 : ℝ) 1 ∧
    (coherenceIndex b (fun j => observableGraph (A j)) rho = 0 ↔
      ∀ j, observableCommutator (observableGraph (A j)) rho = 0) ∧
    ((∃ f : H, ‖f‖ = (1 : ℝ) ∧ rho = InnerProductSpace.rankOne ℂ f f) →
      coherenceIndex b (fun j => observableGraph (A j)) rho = 1) := by sorry

end ObservableCoherence

end QAlgorithms.Papers.Independent.Next46.P31

end
