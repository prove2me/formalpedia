-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_commutative_anchor_determines
-- name    : QAlgorithms.Papers.Independent.Next46.P06.commutative_anchor_determines
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:34:27.424348+00:00
-- url     : https://prove2.me/theorems/ac4e9c67-2420-457d-a90a-44ad75dd1c86
-- title:
--   Theorem 4.1
-- statement:
--   Let $\Phi:F\to\mathcal C(X)$ be a calculus on a complex Banach space, with $F$ a commutative unital complex algebra. Let $f\in F$ and let $E\subseteq\operatorname{reg}(f,\Phi)$ be an anchor set. Then $E$ determines $\Phi$ at $f$:
--
--   $$ (x,y)\in\Phi(f)\iff \Phi(ef)x=\Phi(e)y\quad\text{for every }e\in E.$$
--
--   Here $\operatorname{reg}(f,\Phi)$ consists of the symbols $e$ for which both $\Phi(e)$ and $\Phi(ef)$ are everywhere bounded; an anchor is nonempty and has trivial common kernel. This is determination by individual regularizers, not universal regularizers.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 7, Theorem 4.1

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

/-- Theorem 4.1, PDF p.7. reg(f,Phi) is the individual regularizer set;
the proof's printed reg(Phi,F) is not substituted for it. -/
theorem commutative_anchor_determines [CompleteSpace X] (Phi : F → Graph X) (hPhi : AbstractCalculus Phi)
    (hcomm : ∀ f g : F, f * g = g * f) (f : F) (E : Set F)
    (hE : E ⊆ regularizers Phi f) (hanchor : AnchorSet Phi E) :
    Determines Phi E f := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
