-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_anchored_uniqueness
-- name    : QAlgorithms.Papers.Independent.Next46.P06.anchored_uniqueness
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:36:44.769196+00:00
-- url     : https://prove2.me/theorems/37421307-02e6-4022-a522-cf1e46541723
-- title:
--   Theorem 5.2 (Uniqueness)
-- statement:
--   Let $\Phi,\Psi:F\to\mathcal C(X)$ be calculi on a complex Banach space and a unital complex algebra. Suppose $E\subseteq F$ satisfies $\Phi(e)=\Psi(e)\in\mathcal L(X)$ for every $e\in E$, and that each $f\in F$ is anchored in $E$ with respect to either calculus. Then
--
--   $$\Phi=\Psi.$$
--
--   Anchoring uses the nonempty set $[f]_E$ and its trivial common kernel. Only agreement on $E$ is a hypothesis; agreement on additional products is not imposed.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 10, Theorem 5.2 (Uniqueness)

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

/-- Theorem 5.2 (Uniqueness), PDF p.10. Agreement is assumed only on E;
no additional agreement on products ef is imposed. -/
theorem anchored_uniqueness [CompleteSpace X] (Phi Psi : F → Graph X) (hPhi : AbstractCalculus Phi)
    (hPsi : AbstractCalculus Psi) (E : Set F)
    (hagree : ∀ e ∈ E, Phi e = Psi e ∧ Bounded (Phi e))
    (hanchor : AnchoredSet Phi E Set.univ ∨ AnchoredSet Psi E Set.univ) :
    Phi = Psi := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
