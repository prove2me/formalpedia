-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_pullback_regular_iff
-- name    : QAlgorithms.Papers.Independent.Next46.P06.pullback_regular_iff
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:37:46.179717+00:00
-- url     : https://prove2.me/theorems/f84a7e39-b7dd-4229-8be0-30fb858d1ab7
-- title:
--   Corollary 5.5
-- statement:
--   Let $F,G$ be unital complex algebras, $X$ a complex Banach space, $\Phi:F\to\mathcal C(X)$ a proto-calculus, and $\eta:G\to F$ a unital complex algebra homomorphism. Then
--
--   $$\Phi\circ\eta\text{ is a calculus}\iff\Phi|_{\eta(G)}\text{ is a calculus}.$$
--
--   Thus regularity of the mapping is exactly regularity of its image subalgebra, without requiring $\eta$ to be injective.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 11, Corollary 5.5

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

/-- Corollary 5.5, PDF p.11: regularity of the pull-back equals regularity of
restriction to the image; no injectivity of eta is required. -/
theorem pullback_regular_iff [CompleteSpace X] (Phi : F → Graph X) (hPhi : Proto Phi)
    (eta : G →ₐ[ℂ] F) :
    AbstractCalculus (pullback Phi eta) ↔ CalculusOn Phi (Set.range eta) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
