-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_extension_exists_unique
-- name    : QAlgorithms.Papers.Independent.Next46.P06.extension_exists_unique
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:39:45.898978+00:00
-- url     : https://prove2.me/theorems/0ad6b622-b3ba-480e-812b-f84d0013e01e
-- title:
--   Theorem 6.1 (Extension Theorem)
-- statement:
--   Let $F$ be a unital complex algebra, $E\subseteq F$ a possibly nonunital complex subalgebra, and $X$ a complex Banach space. Let $\rho:E\to\mathcal L(X)$ be a complex algebra representation, not assumed unital. Suppose every $f\in F$ is anchored in $E$ with respect to $\rho$. There exists a unique calculus $\widehat\Phi:F\to\mathcal C(X)$ extending $\rho$, and its graph is
--
--   $$ (x,y)\in\widehat\Phi(f)\iff\forall e\in[f]_E,\ \rho(ef)x=\rho(e)y.$$
--
--   The existence of closed single-valued values and the calculus axioms are conclusions. Uniqueness ranges over every extending calculus, without imposing the graph formula on competitors. No commutativity or domain density is assumed.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 13, Theorem 6.1 (Extension Theorem)

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

/-- Theorem 6.1 (Extension Theorem), PDF pp.13–14. The representation on E
need not be unital and E need not contain 1. Formula (6.1) specifies the
constructed calculus and does not replace the existence assertion. -/
theorem extension_exists_unique [CompleteSpace X] (rho : F → X →L[ℂ] X) (E : Set F)
    (hrho : AlgebraRepresentationOn rho E)
    (hanchor : AnchoredSet (representationGraphs rho) E Set.univ) :
    ∃ Phi : F → Graph X, AbstractCalculus Phi ∧
      (∀ e ∈ E, Phi e = banachBoundedGraph (rho e)) ∧
      (∀ f, Phi f = canonicalAlgebraicExtension rho E f) ∧
      (∀ Psi : F → Graph X, AbstractCalculus Psi →
        (∀ e ∈ E, Psi e = banachBoundedGraph (rho e)) → Psi = Phi) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
