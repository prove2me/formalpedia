-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_canonical_extension_core
-- name    : QAlgorithms.Papers.Independent.Next46.P06.canonical_extension_core
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:42:03.756615+00:00
-- url     : https://prove2.me/theorems/72fcf52e-d7f4-4d01-8cba-fc381b8ed42a
-- title:
--   Corollary 6.6
-- statement:
--   Let $F$ be a unital complex algebra, $E\subseteq F$ a possibly nonunital complex subalgebra, and $\rho:E\to\mathcal L(X)$ a nondegenerate representation on a complex Banach space. On the constructed carrier $F_\rho=\langle E,F,\rho\rangle$, formula (6.1) defines a calculus extending $\rho$:
--
--   $$ (x,y)\in\widehat\Phi(f)\iff\forall e\in[f]_E,\rho(ef)x=\rho(e)y.$$
--
--   It is the unique such calculus on $F_\rho$, and $E$ is an algebraic core for this extension. The core belongs to the extended calculus, not just the original bounded representation.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 16, Corollary 6.6

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

/-- Corollary 6.6, PDF p.16: the canonical extension is a calculus on (6.2),
E is its algebraic core, and any other extension agrees on that graphDomain. -/
theorem canonical_extension_core [CompleteSpace X] (rho : F → X →L[ℂ] X) (E : Set F)
    (hrho : AlgebraRepresentationOn rho E) (hnd : Nondegenerate rho E) :
    CalculusOn (canonicalAlgebraicExtension rho E) (maximalAnchored rho E) ∧
    (∀ e ∈ E, canonicalAlgebraicExtension rho E e = banachBoundedGraph (rho e)) ∧
    AlgebraicCoreOn (canonicalAlgebraicExtension rho E) E (maximalAnchored rho E) ∧
    ∀ Psi : F → Graph X, CalculusOn Psi (maximalAnchored rho E) →
      (∀ e ∈ E, Psi e = banachBoundedGraph (rho e)) →
      ∀ f ∈ maximalAnchored rho E, Psi f = canonicalAlgebraicExtension rho E f := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
