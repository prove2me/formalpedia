-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P81_strong_iff_joint
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P81.strong_iff_joint
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:02:13.493537+00:00
-- url     : https://prove2.me/theorems/a6efdadd-2b0f-4f9f-ab3e-ac1188e16651
-- title:
--   Strong continuity is equivalent to joint continuity of the unitary action
-- statement:
--   Let $G$ be a Lie group, $\mathcal H$ a possibly infinite-dimensional complex Hilbert space, and $U:G\to\mathcal U(\mathcal H)$ any unitary family. Then
--
--   $$(g,v)\longmapsto U(g)v\text{ is jointly continuous}\quad\Longleftrightarrow\quad U\text{ is continuous in the strong operator topology}.$$
--
--   Here the strong operator topology is pointwise convergence on $\mathcal H$, and $\mathcal H$ has its norm topology. No homomorphism law is assumed. When the family is a homomorphism, this equivalence gives precisely the continuous representation asserted in Appendix A.2.
-- source:
--   Symmetries in quantum field theory and quantum gravity, arXiv:1810.05338v2, PDF p. 139, Theorem C.1: strong and joint action continuity

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

/-- Theorem C.1, PDF pp.139--140 (announced on p.138).
No homomorphism law is imposed on U. For a homomorphism the left side is exactly
continuity of its representation action, as in Appendix A.2.
Printed p.138: boundedness uses a strict inequality even at v=0.
Changed: use standard bounded Hilbert operators. Why: the literal bound fails at zero. -/
theorem strong_iff_joint (U : G → H ≃ₗᵢ[ℂ] H) :
    Continuous (fun p : G × H => U p.1 p.2) ↔ (∀ v : H, Continuous (fun g => U g v)) := by sorry

end Lie

end Hilbert

end QAlgorithms.Papers.Independent.Intakenext100.P81

end
