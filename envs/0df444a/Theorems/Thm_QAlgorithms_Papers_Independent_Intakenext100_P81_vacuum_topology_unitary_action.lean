-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P81_vacuum_topology_unitary_action
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P81.vacuum_topology_unitary_action
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:03:45.860127+00:00
-- url     : https://prove2.me/theorems/1112241d-4cfb-41cd-ba8a-4aacb533f128
-- title:
--   Vacuum topology gives a continuous unitary action on the Hilbert completion
-- statement:
--   Under the assumptions of Theorem C.3, assume also that $\Omega$ is separating for $\mathcal A$ and that $U(g)^\dagger\mathcal A U(g)\subseteq\mathcal A$ for every $g$. Give $\mathcal A$ the vacuum inner product and its induced topology,
--
--   $$\langle O,P\rangle_\Omega=\langle O\Omega,P\Omega\rangle.$$
--
--   Conjugation is jointly continuous in this topology on all of $G\times\mathcal A$, without restricting the operator argument to a uniformly bounded set, and preserves this inner product. If $U$ is a homomorphism, inverse-indexed conjugation defines a strongly continuous unitary representation on the Hilbert completion:
--
--   $$\rho(g)(O\Omega)=\bigl(U(g^{-1})^\dagger O U(g^{-1})\bigr)\Omega.$$
--
--   Evaluation $O\mapsto O\Omega$ is injective and has dense range, so this completion is canonically realized by the original Hilbert space. Completion and inverse indexing correct the source’s incomplete-space and action-order typing issues while preserving its continuity and unitarity content.
-- source:
--   Symmetries in quantum field theory and quantum gravity, arXiv:1810.05338v2, PDF p. 143, Theorem C.4: vacuum topology and unitary action

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P81

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P81

open scoped BigOperators ComplexConjugate Manifold ContDiff

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [hilbertComplete : CompleteSpace H]

section Lie

variable {m : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [lieCharts : ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
  [lieSmooth : LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G]
  [lieHausdorff : T2Space G] [lieSecondCountable : SecondCountableTopology G]

include hilbertComplete lieCharts lieSmooth lieHausdorff lieSecondCountable

/-- Theorem C.4, PDF pp.142--143. Corrected typing: use the Hilbert completion
of the vacuum inner-product algebra and inverse-indexed conjugation for a left action.
The completion is realized by H: evaluation O↦OΩ is injective (separating) and dense
(cyclic), and its pulled-back inner product is vacuumInner. No completeness of A is assumed.
Printed: p.138 has a strict bound at zero; p.142 excludes even the zero annihilator;
pp.142-143 call A itself Hilbert and direct conjugation a left representation, and omit
algebra preservation from the standalone theorem.
Changed: allow zero in the bound and require only zero annihilators, use the completion
and inverse indexing, and include preservation as in (C.5).
Why: zero cases otherwise vacuate the hypotheses; completion, action order and the
codomain must be correctly typed. All continuity and unitarity conclusions remain. -/
theorem vacuum_topology_unitary_action (U : G → H ≃ₗᵢ[ℂ] H)
    (A : Subalgebra ℂ (H →L[ℂ] H)) (vac : H) (hnorm : ‖vac‖ = 1)
    (hcyclic : IsCyclic A vac) (hseparating : VacuumSeparating A vac)
    (hfixed : ∀ g, U g vac = vac) (hconj : BoundedConjugationContinuous U A)
    (hpreserve : ∀ g (O : A), adjointConjugationCLM (U g) (O : H →L[ℂ] H) ∈ A) :
    VacuumConjugationContinuous U A vac ∧
    (∀ g (O P : A),
      vacuumInner vac (adjointConjugationCLM (U g) (O : H →L[ℂ] H))
        (adjointConjugationCLM (U g) (P : H →L[ℂ] H)) =
      vacuumInner vac (O : H →L[ℂ] H) (P : H →L[ℂ] H)) ∧
    (Function.Injective (fun O : A => (O : H →L[ℂ] H) vac) ∧
      DenseRange (fun O : A => (O : H →L[ℂ] H) vac)) ∧
    ((∀ g h, U (g * h) = U g * U h) →
      ∃ rho : G →* (H ≃ₗᵢ[ℂ] H), (∀ v : H, Continuous (fun g => rho g v)) ∧
        ∀ g (O : A), rho g ((O : H →L[ℂ] H) vac) =
          adjointConjugationCLM (U (g⁻¹)) (O : H →L[ℂ] H) vac) := by sorry

end Lie

end Hilbert

end QAlgorithms.Papers.Independent.Intakenext100.P81

end
