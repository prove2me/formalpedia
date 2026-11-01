-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P81_bounded_conjugation_continuous
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P81.bounded_conjugation_continuous
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:02:39.897488+00:00
-- url     : https://prove2.me/theorems/1f5df216-fcbf-4f76-b360-544107f68d13
-- title:
--   Conjugation is jointly strongly continuous on uniformly bounded sets
-- statement:
--   Let $G$ be a Lie group, $\mathcal H$ a complex Hilbert space, and $U:G\to\mathcal U(\mathcal H)$ a strongly continuous unitary family. Let $M\subseteq B(\mathcal H)$ have one finite common operator-norm bound: $\|O\|\le C$ for all $O\in M$. Then
--
--   $$G\times M\longrightarrow B(\mathcal H),\qquad(g,O)\longmapsto U(g)^\dagger OU(g)$$
--
--   is continuous when $M$ and $B(\mathcal H)$ carry the strong operator topology. The bound is uniform over $M$; no homomorphism law or invariant vector is required. This gives the bounded-set continuity used for local symmetry actions.
-- source:
--   Symmetries in quantum field theory and quantum gravity, arXiv:1810.05338v2, PDF p. 140, Theorem C.2: bounded-set conjugation continuity

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

/-- Theorem C.2, PDF pp.140--141. The operator argument has strong topology,
and its domain is restricted to a single uniformly bounded set.
Printed p.138: the common bound is strict for every vector, including zero.
Changed: use a non-strict common bound. Why: the printed inequality fails at zero. -/
theorem bounded_conjugation_continuous (U : G → H ≃ₗᵢ[ℂ] H)
    (hU : (∀ v : H, Continuous (fun g => U g v))) (M : Set (H →Lₚₜ[ℂ] H)) (hM : UniformlyBounded M) :
    Continuous (fun p : G × M =>
      (adjointConjugationCLM (U p.1) (p.2.val : H →L[ℂ] H) : H →Lₚₜ[ℂ] H)) := by sorry

end Lie

end Hilbert

end QAlgorithms.Papers.Independent.Intakenext100.P81

end
