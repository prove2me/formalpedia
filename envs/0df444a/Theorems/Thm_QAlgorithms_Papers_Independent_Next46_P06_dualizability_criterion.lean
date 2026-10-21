-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_dualizability_criterion
-- name    : QAlgorithms.Papers.Independent.Next46.P06.dualizability_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:44:25.055686+00:00
-- url     : https://prove2.me/theorems/95c23a8f-4a86-4bce-b631-e98514d3765a
-- title:
--   §8, unnumbered: dualizability criterion
-- statement:
--   Let $\Phi:F\to\mathcal C(X)$ be a calculus on a complex Banach space, $B=\operatorname{bdd}(F,\Phi)$, and let $(F',\Phi')$ be its canonical dual calculus in the opposite algebra. Then
--
--   $$F'=F^{\mathrm{op}}\iff\forall f\in F\ \forall b\in B,\ \operatorname{span}\{\Phi(e)x:x\in X,\ e\in B,\ fbe\in B\}\text{ is dense in }X.$$
--
--   Under these equivalent conditions the bounded parts of the original and dual calculi coincide, after identifying their underlying carriers. This is the explicit dualizability criterion, without adding an informal maximality claim.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 21, §8, unnumbered: dualizability criterion

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

/-- Section 8, PDF p.21: the explicit dualizability criterion and equality
of bounded parts; the narrative maximality sentence is not added. -/
theorem dualizability_criterion [CompleteSpace X] (Phi : F → Graph X) (hPhi : AbstractCalculus Phi) :
    (dualDomain Phi = Set.univ ↔
      ∀ f b, b ∈ boundedElements Phi → Dense (dualizableRangeSpan Phi f b)) ∧
    (dualDomain Phi = Set.univ →
      boundedElements Phi = {f | f ∈ dualDomain Phi ∧ Bounded (dualEvaluation Phi f)}) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
