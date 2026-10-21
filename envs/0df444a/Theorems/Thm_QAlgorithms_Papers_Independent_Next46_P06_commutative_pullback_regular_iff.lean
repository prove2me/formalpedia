-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_commutative_pullback_regular_iff
-- name    : QAlgorithms.Papers.Independent.Next46.P06.commutative_pullback_regular_iff
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:38:49.503609+00:00
-- url     : https://prove2.me/theorems/4a66596c-3029-40bb-bb89-f0930f33de43
-- title:
--   Corollary 5.7
-- statement:
--   Let $F$ be a commutative unital complex algebra, $G$ a unital complex algebra, $X$ a complex Banach space, $\Phi:F\to\mathcal C(X)$ a calculus, and $\eta:G\to F$ a unital complex homomorphism. Then
--
--   $$\Phi\circ\eta\text{ is a calculus}\iff\forall g\in G,\ \operatorname{reg}(\eta(g),\Phi)\cap\eta(G)\text{ is a }\Phi\text{-anchor}.$$
--
--   Commutativity is required of $F$, with no injectivity hypothesis on $\eta$.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 12, Corollary 5.7

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

/-- Corollary 5.7, PDF p.12: anchor criterion on the image of eta. -/
theorem commutative_pullback_regular_iff [CompleteSpace X] (Phi : F → Graph X) (hPhi : AbstractCalculus Phi)
    (hcomm : ∀ f g : F, f * g = g * f) (eta : G →ₐ[ℂ] F) :
    AbstractCalculus (pullback Phi eta) ↔
      ∀ g : G, AnchorSet Phi (regularizers Phi (eta g) ∩ Set.range eta) := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
