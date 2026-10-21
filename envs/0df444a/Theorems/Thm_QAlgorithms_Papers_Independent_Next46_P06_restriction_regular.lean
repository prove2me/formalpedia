-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_restriction_regular
-- name    : QAlgorithms.Papers.Independent.Next46.P06.restriction_regular
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:38:18.754774+00:00
-- url     : https://prove2.me/theorems/31d6ab96-75be-4350-a47b-aaef34bc0b7c
-- title:
--   Theorem 5.6
-- statement:
--   Let $F$ be a commutative unital complex algebra, $X$ a complex Banach space, and $\Phi:F\to\mathcal C(X)$ a calculus. Let $S$ be a unital complex subalgebra such that
--
--   $$\operatorname{reg}(g,\Phi)\cap S\text{ is a }\Phi\text{-anchor for every }g\in S.$$
--
--   Then $\Phi|_S$ is a calculus. Anchors are nonempty and consist of bounded symbols; no dense-domain condition is added.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 12, Theorem 5.6

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

/-- Theorem 5.6, PDF p.12: the regularity criterion for a unital subalgebra of
a commutative algebra. -/
theorem restriction_regular [CompleteSpace X] (Phi : F → Graph X) (hPhi : AbstractCalculus Phi)
    (hcomm : ∀ f g : F, f * g = g * f) (S : Subalgebra ℂ F)
    (hanchor : ∀ g : S, AnchorSet Phi (regularizers Phi (g : F) ∩ (S : Set F))) :
    CalculusOn Phi (S : Set F) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
