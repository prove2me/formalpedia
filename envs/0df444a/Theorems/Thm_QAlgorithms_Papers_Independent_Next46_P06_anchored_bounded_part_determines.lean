-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_anchored_bounded_part_determines
-- name    : QAlgorithms.Papers.Independent.Next46.P06.anchored_bounded_part_determines
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:35:13.123963+00:00
-- url     : https://prove2.me/theorems/7fe2080b-91e5-4b40-aa53-70d3a4e918d0
-- title:
--   Theorem 4.2
-- statement:
--   Let $\Phi:F\to\mathcal C(X)$ be a calculus, where $F$ is a unital complex algebra and $X$ is a complex Banach space. Suppose $E\subseteq\operatorname{bdd}(F,\Phi)$ and every bounded symbol $g$ is anchored in $E$, meaning that $[g]_E=\{e\in E:eg\in E\}$ is a nonempty common-kernel anchor. Then $E$ determines $\Phi$ on every symbol. If $E$ is also closed under multiplication, it is an algebraic core:
--
--   $$ E\text{ multiplicative}\ \Longrightarrow\ \forall f\in F,\ [f]_E\text{ determines }\Phi\text{ at }f.$$
--
--   No commutativity hypothesis is imposed on $F$.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 8, Theorem 4.2

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Theorem 4.2, PDF pp.8–10: both determination and the multiplicative-core
conclusion are retained, without an ambient commutativity hypothesis. -/
theorem anchored_bounded_part_determines [CompleteSpace X] (Phi : F → Graph X) (hPhi : AbstractCalculus Phi)
    (E : Set F) (hE : E ⊆ boundedElements Phi)
    (hanchor : AnchoredSet Phi E (boundedElements Phi)) :
    (∀ f, Determines Phi E f) ∧
    (MulClosedSet E → AlgebraicCoreOn Phi E Set.univ) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
