-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_nondegeneracy_equivalences
-- name    : QAlgorithms.Papers.Independent.Next46.P06.nondegeneracy_equivalences
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:40:37.623333+00:00
-- url     : https://prove2.me/theorems/d4cd15d4-0152-47cc-b7f0-1cdf8ff7d507
-- title:
--   Lemma 6.2
-- statement:
--   Let $F$ be a unital complex algebra, $E\subseteq F$ a possibly nonunital complex subalgebra, and $\rho:E\to\mathcal L(X)$ a representation on a complex Banach space. Write
--
--   $$\langle E,F,\rho\rangle=\{f\in F:\forall e\in E,\ [ef]_E\text{ is a }\rho\text{-anchor}\}.$$
--
--   The following are equivalent: $E$ is an anchor; $1$ is anchored in $E$; and both $E$ and $\langle E,F,\rho\rangle$ are nonempty. An anchor retains its explicit nonempty requirement, including on the zero Banach space.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 15, Lemma 6.2

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

/-- Lemma 6.2, PDF p.15: all three equivalent nondegeneracy conditions,
with the nonempty requirements explicit. -/
theorem nondegeneracy_equivalences [CompleteSpace X] (rho : F → X →L[ℂ] X) (E : Set F)
    (hrho : AlgebraRepresentationOn rho E) :
    (AnchorSet (representationGraphs rho) E ↔ Anchored (representationGraphs rho) E 1) ∧
    (AnchorSet (representationGraphs rho) E ↔ E.Nonempty ∧ (maximalAnchored rho E).Nonempty) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
