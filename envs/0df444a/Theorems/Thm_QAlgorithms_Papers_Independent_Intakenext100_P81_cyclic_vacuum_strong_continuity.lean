-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P81_cyclic_vacuum_strong_continuity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P81.cyclic_vacuum_strong_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:03:11.457302+00:00
-- url     : https://prove2.me/theorems/de9e2f2b-c6e3-4e24-8eb3-98317b11d16b
-- title:
--   A cyclic invariant vector recovers strong continuity
-- statement:
--   Let $G$ be a Lie group, $\mathcal H$ a complex Hilbert space, $\mathcal A\subseteq B(\mathcal H)$ a unital complex subalgebra, and $U(g)$ a unitary family. Suppose conjugation $(g,O)\mapsto U(g)^\dagger OU(g)$ is jointly strongly continuous on $G\times M$ for every uniformly bounded subset $M\subseteq\mathcal A$. Suppose a unit vector $\Omega$ is fixed by every $U(g)$ and is cyclic, meaning $\mathcal A\Omega$ is dense in $\mathcal H$. Then
--
--   $$U:G\longrightarrow\mathcal U(\mathcal H)\text{ is strongly continuous}.$$
--
--   The result recovers continuity on the whole Hilbert space from bounded-set continuity on an algebra with an invariant cyclic state. No group multiplication law is imposed on the family.
-- source:
--   Symmetries in quantum field theory and quantum gravity, arXiv:1810.05338v2, PDF p. 141, Theorem C.3: recover strong continuity from a cyclic invariant vector

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

/-- Theorem C.3, PDF pp.141--142. The invariant cyclic state is normalized.
No group law for the unitary family is assumed; adjoints suffice in the proof.
Printed p.138: uniform boundedness is strict even at the zero vector.
Changed: UniformlyBounded uses a common non-strict bound. Why: zero must be allowed. -/
theorem cyclic_vacuum_strong_continuity (U : G → H ≃ₗᵢ[ℂ] H)
    (A : Subalgebra ℂ (H →L[ℂ] H)) (vac : H) (hnorm : ‖vac‖ = 1)
    (hcyclic : IsCyclic A vac) (hfixed : ∀ g, U g vac = vac)
    (hconj : BoundedConjugationContinuous U A) :
    (∀ v : H, Continuous (fun g => U g v)) := by sorry

end Lie

end Hilbert

end QAlgorithms.Papers.Independent.Intakenext100.P81

end
