-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_compatibility_criteria
-- name    : QAlgorithms.Papers.Independent.Next46.P06.compatibility_criteria
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:39:13.959559+00:00
-- url     : https://prove2.me/theorems/1876395b-fa17-4900-8a20-11d45048f1c1
-- title:
--   Theorem 5.8
-- statement:
--   Let $F,G$ be unital complex algebras and $X$ a complex Banach space. Let $\eta:G\to F$ be a unital complex homomorphism and let $\Phi:F\to\mathcal C(X)$ and $\Psi:G\to\mathcal C(X)$ be proto-calculi. Suppose $E$ is an algebraic core for $\Psi$ and $\Phi(\eta(e))=\Psi(e)$ for $e\in E$. Then
--
--   $$\Phi\circ\eta=\Psi\iff\Phi|_{\eta(G)}\text{ is a calculus}\iff\eta(E)\text{ is an algebraic core for }\Phi|_{\eta(G)}.$$
--
--   All three conditions hold if $\Phi$ is a calculus and $F$ is commutative. This records both the equivalences and the final sufficient condition.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 12, Theorem 5.8

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

/-- Theorem 5.8, PDF p.12: the three equivalent criteria, and the final
sufficient condition, without adding agreement on products. -/
theorem compatibility_criteria [CompleteSpace X] (Phi : F → Graph X) (Psi : G → Graph X)
    (hPhi : Proto Phi) (hPsi : Proto Psi) (eta : G →ₐ[ℂ] F)
    (E : Set G) (hcore : AlgebraicCoreOn Psi E Set.univ)
    (hagree : ∀ e ∈ E, Phi (eta e) = Psi e) :
    ((pullback Phi eta = Psi) ↔ CalculusOn Phi (Set.range eta)) ∧
    ((pullback Phi eta = Psi) ↔ AlgebraicCoreOn Phi (eta '' E) (Set.range eta)) ∧
    (AbstractCalculus Phi → (∀ f g : F, f * g = g * f) →
      pullback Phi eta = Psi ∧ CalculusOn Phi (Set.range eta) ∧
        AlgebraicCoreOn Phi (eta '' E) (Set.range eta)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
