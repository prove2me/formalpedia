-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_bounded_calculi
-- name    : QAlgorithms.Papers.Independent.Next46.P06.bounded_calculi
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:33:50.698072+00:00
-- url     : https://prove2.me/theorems/97e5670b-b886-4696-8734-fed2e1c88129
-- title:
--   Example 3.3 (Bounded (Proto-)Calculi)
-- statement:
--   Let $F$ be a unital complex algebra and $X$ a complex Banach space. A map $\Phi:F\to\mathcal C(X)$ is a proto-calculus with every value everywhere bounded if and only if it is the graph-valued form of a unital complex algebra representation $\rho:F\to\mathcal L(X)$:
--
--   $$\Phi(f)=\operatorname{graph}(\rho(f))\qquad(f\in F).$$
--
--   Every such representation satisfies FC4 and therefore is a calculus. No topological continuity in the symbol algebra is required.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 7, Example 3.3 (Bounded (Proto-)Calculi)

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

/-- Example 3.3, PDF p.7: bounded proto-calculi are exactly unital bounded
representations, and every such representation satisfies FC4. -/
theorem bounded_calculi [CompleteSpace X] (Phi : F → Graph X) :
    ((Proto Phi ∧ ∀ f, Bounded (Phi f)) ↔
      ∃ rho : F →ₐ[ℂ] (X →L[ℂ] X), ∀ f, Phi f = banachBoundedGraph (rho f)) ∧
    (∀ rho : F →ₐ[ℂ] (X →L[ℂ] X), AbstractCalculus (fun f => banachBoundedGraph (rho f))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
