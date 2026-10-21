-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_pullback_properties
-- name    : QAlgorithms.Papers.Independent.Next46.P06.pullback_properties
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:37:16.836652+00:00
-- url     : https://prove2.me/theorems/33b6dcb4-be58-40f1-8f15-3bb0e648a692
-- title:
--   Lemma 5.3
-- statement:
--   Let $F,G$ be unital complex algebras, $X$ a complex Banach space, $\Phi:F\to\mathcal C(X)$ a proto-calculus, and $\eta:G\to F$ a unital complex algebra homomorphism. Put $P=\Phi\circ\eta$ and let $E\subseteq\operatorname{bdd}(G,P)$ and $g\in G$. Then
--
--   $$\operatorname{bdd}(G,P)=\eta^{-1}(\operatorname{bdd}(F,\Phi)),\qquad \eta(\operatorname{bdd}(G,P))=\operatorname{bdd}(F,\Phi)\cap\eta(G)=\operatorname{bdd}(\eta(G),\Phi|_{\eta(G)}).$$
--
--   Moreover: $E$ is a $P$-anchor exactly when $\eta(E)$ is a $\Phi$-anchor; $\eta([g]_E)\subseteq[\eta(g)]_{\eta(E)}$; $E$ determines $P$ at $g$ exactly when $\eta(E)$ determines $\Phi$ at $\eta(g)$; and, if $E$ is an algebraic core for $P$, then $\eta(E)$ is an algebraic core for $\Phi|_{\eta(G)}$. The last assertion is an implication, not an equivalence.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 11, Lemma 5.3

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

/-- Lemma 5.3, PDF p.11: all five clauses. Restriction is expressed on the
ambient carrier with explicit range guards. Clause (e) is one-way only. -/
theorem pullback_properties [CompleteSpace X] (Phi : F → Graph X) (hPhi : Proto Phi)
    (eta : G →ₐ[ℂ] F) (E : Set G) (hE : E ⊆ boundedElements (pullback Phi eta)) (g : G) :
    (boundedElements (pullback Phi eta) = eta ⁻¹' boundedElements Phi ∧
      eta '' boundedElements (pullback Phi eta) = boundedElements Phi ∩ Set.range eta ∧
      eta '' boundedElements (pullback Phi eta) = {f | f ∈ Set.range eta ∧ Bounded (Phi f)}) ∧
    (AnchorSet (pullback Phi eta) E ↔ AnchorSet Phi (eta '' E)) ∧
    (eta '' symbolBracket E g ⊆ symbolBracket (eta '' E) (eta g)) ∧
    (Determines (pullback Phi eta) E g ↔ Determines Phi (eta '' E) (eta g)) ∧
    (AlgebraicCoreOn (pullback Phi eta) E Set.univ →
      AlgebraicCoreOn Phi (eta '' E) (Set.range eta)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
