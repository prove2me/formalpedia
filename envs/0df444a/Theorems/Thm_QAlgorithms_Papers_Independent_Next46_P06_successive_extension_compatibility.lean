-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_successive_extension_compatibility
-- name    : QAlgorithms.Papers.Independent.Next46.P06.successive_extension_compatibility
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:42:36.406913+00:00
-- url     : https://prove2.me/theorems/c51f8e58-5687-4ed4-a1a7-04a25fbf99fb
-- title:
--   Theorem 6.7
-- statement:
--   Let $S$ be a unital subalgebra of a unital complex algebra $G$. Let $\Phi:S\to\mathcal C(X)$ be a calculus on a complex Banach space, and let a subalgebra $E\subseteq S$ be its algebraic core. Let $E'\subseteq G$ be a subalgebra containing $E$, with a bounded representation $\rho$ agreeing with $\Phi$ on $E$. Put $S'=\langle E',G,\rho\rangle$ and let $\Psi$ be its canonical extension. For $f\in S$,
--
--   $$f\in S'\quad\text{and}\quad\Phi(f)=\Psi(f)$$
--
--   if any of these seven conditions holds: (1) $f\in S'$ and $\Psi(f)$ is bounded; (2) $f\in S'$, $\Psi(f)$ is densely defined, and $\Phi(f)$ is bounded; (3) for every $e'\in E'$ there is a $\rho$-anchor $M_{e'}\subseteq E'$ with $M_{e'}e'\subseteq D'[f]_E$, where $D'=\{d\in S':dE\subseteq E'\}$; (4) $E'=E$; (5) $Z(E')\cap[f]_E$ is an anchor; (6) $E\subseteq Z(E')$; (7) $E'$ is commutative. The undefined printed symbol $\Phi'$ in (1),(2) is read as the just-introduced $\Psi$, pending independent moderation.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 16, Theorem 6.7

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

/-- Theorem 6.7, PDF pp.16–18: all seven sufficient alternatives in the
successive-extension setup. Printed: Phi-prime in (1),(2) and the proof is
undefined. Changed: it denotes the canonical extension of Psi just introduced.
Why: the immediately preceding setup and the inclusion proof identify that map.
This transparent symbol correction requires independent moderation. -/
theorem successive_extension_compatibility [CompleteSpace X] (S : Subalgebra ℂ F)
    (Phi : F → Graph X) (hPhi : CalculusOn Phi (S : Set F)) (E Ep : Set F)
    (hEalg : SubalgebraSet E) (hcore : AlgebraicCoreOn Phi E (S : Set F))
    (rho : F → X →L[ℂ] X) (hrho : AlgebraRepresentationOn rho Ep)
    (hEEp : E ⊆ Ep) (hagree : ∀ e ∈ E, Phi e = banachBoundedGraph (rho e))
    (f : F) (hf : f ∈ S)
    (hcriterion :
      (f ∈ maximalAnchored rho Ep ∧ Bounded (canonicalAlgebraicExtension rho Ep f)) ∨
      (f ∈ maximalAnchored rho Ep ∧ Dense (graphDomain (canonicalAlgebraicExtension rho Ep f)) ∧ Bounded (Phi f)) ∨
      (∀ ep ∈ Ep, ∃ M : Set F, M ⊆ Ep ∧ AnchorSet (representationGraphs rho) M ∧
        setProduct M {ep} ⊆
          setProduct {d | d ∈ maximalAnchored rho Ep ∧ ∀ e ∈ E, d * e ∈ Ep} (symbolBracket E f)) ∨
      Ep = E ∨
      AnchorSet (representationGraphs rho) (setCenter Ep ∩ symbolBracket E f) ∨
      E ⊆ setCenter Ep ∨ CommutativeSet Ep) :
    f ∈ maximalAnchored rho Ep ∧ Phi f = canonicalAlgebraicExtension rho Ep f := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
