-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_core_agreement_inclusion
-- name    : QAlgorithms.Papers.Independent.Next46.P06.core_agreement_inclusion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:36:09.600999+00:00
-- url     : https://prove2.me/theorems/38dbba5d-3793-4681-9d5c-dbb61f9bb40c
-- title:
--   Lemma 5.1
-- statement:
--   Let $\Phi,\Psi:F\to\mathcal C(X)$ be proto-calculi on a complex Banach space, with $F$ a unital complex algebra. Let $E\subseteq F$ be an algebraic core for $\Psi$, and suppose the two maps agree on $E$. Then
--
--   $$\Phi(f)\subseteq\Psi(f)\qquad(f\in F).$$
--
--   If $E$ is also an algebraic core for $\Phi$, then $\Phi=\Psi$. Inclusion is graph inclusion, including domain inclusion; agreement on products outside $E$ is not assumed.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 10, Lemma 5.1

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

/-- Lemma 5.1, PDF p.10: graph inclusion in the stated direction, and equality
when E is a core for both proto-calculi. -/
theorem core_agreement_inclusion [CompleteSpace X] (Phi Psi : F → Graph X)
    (hPhi : Proto Phi) (hPsi : Proto Psi) (E : Set F)
    (hagree : ∀ e ∈ E, Phi e = Psi e) (hcore : AlgebraicCoreOn Psi E Set.univ) :
    (∀ f, Phi f ⊆ Psi f) ∧ (AlgebraicCoreOn Phi E Set.univ → Phi = Psi) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
