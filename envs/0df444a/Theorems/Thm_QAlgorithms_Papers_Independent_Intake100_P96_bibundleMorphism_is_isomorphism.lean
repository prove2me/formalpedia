-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P96_bibundleMorphism_is_isomorphism
-- name    : QAlgorithms.Papers.Independent.Intake100.P96.bibundleMorphism_is_isomorphism
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:56:03.569881+00:00
-- url     : https://prove2.me/theorems/165b3472-0c39-4af3-9fc9-e3604f09c497
-- title:
--   Every smooth principal-bibundle morphism over a fixed base is an isomorphism
-- statement:
--   Let $H$ be a finite-dimensional real Lie group, and let $E\to M$ and $F\to M$ be smooth principal $H$-bibundles over the same Hausdorff paracompact smooth manifold $M$. Both actions are free and transitive on each fibre, commute with one another, and admit smooth local trivializations. If $W:E\to F$ is smooth, preserves the projection, and intertwines both actions, then it has a smooth inverse $V:F\to E$ that also preserves the projection and both actions:
--
--   $$V\circ W=\operatorname{id}_E,\qquad W\circ V=\operatorname{id}_F.$$
--
--   Thus morphisms of these principal bibundles are isomorphisms; no inverse or bijectivity is assumed.
-- source:
--   Nonabelian Bundle Gerbes, their Differential Geometry and Gauge Theory, arXiv:hep-th/0312154v2, PDF p. 4, §2, unnumbered: bibundle morphisms are isomorphisms

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P96

open scoped Manifold ContDiff

namespace QAlgorithms.Papers.Independent.Intake100.P96

universe u v w z

section Bundles

variable {m h e : ℕ} {M : Type u} {H : Type v} {E : Type w}

variable [TopologicalSpace M] [ChartedSpace (RealModel m) M]

variable [TopologicalSpace H] [ChartedSpace (RealModel h) H]

variable [TopologicalSpace E] [ChartedSpace (RealModel e) E]

variable [Group H]

section Morphisms

variable {d : ℕ} {F : Type z}

variable [TopologicalSpace F] [ChartedSpace (RealModel d) F]

/-- Unnumbered result after (2), PDF p. 4: every morphism of principal
bibundles over the SAME base is a smooth isomorphism of bibundles.
The inverse, its smoothness and its equivariance are conclusions. -/
theorem bibundleMorphism_is_isomorphism
    (B : LeftPrincipalBundle m h e M H E) (R : RightPrincipalStructure B)
    (C : LeftPrincipalBundle m h d M H F) (S : RightPrincipalStructure C)
    (W : E → F) (morphism : IsBibundleMap B R C S W) :
    ∃ V : F → E, IsBibundleMap C S B R V ∧
      Function.LeftInverse V W ∧ Function.RightInverse V W := by sorry

end Morphisms

end Bundles

end QAlgorithms.Papers.Independent.Intake100.P96
