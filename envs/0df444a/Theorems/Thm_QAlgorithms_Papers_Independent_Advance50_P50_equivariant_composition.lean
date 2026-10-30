-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P50_equivariant_composition
-- name    : QAlgorithms.Papers.Independent.Advance50.P50.equivariant_composition
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:22:06.24371+00:00
-- url     : https://prove2.me/theorems/36877200-a3f2-4b79-941f-40e733d2b4c7
-- title:
--   Unnumbered invariant composition criterion
-- statement:
--   Let a group $G$ act on spaces $A_0,\ldots,A_M$, and let $f_j:A_j\to A_{j+1}$ be equivariant for $0\le j<M$. Let $q:A_M\to B$ be invariant, where $B$ has trivial action. The maps need not be linear or quantum channels. Then
--
--   $$q\circ f_{M-1}\circ\cdots\circ f_0(g\cdot x)=q\circ f_{M-1}\circ\cdots\circ f_0(x).$$
--
--   The constructed composition is invariant. When $M=0$, it is simply the final invariant map $q$.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, PDF p. 16, Unnumbered invariant composition criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory

open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.16: equivariant intermediate maps followed by an invariant final
map yield an invariant model. M counts intermediate maps, so M=0 is allowed. -/
theorem equivariant_composition {G : Type*} [Group G] {A : ℕ → Type*} {B : Type*}
    (action : ∀ j, G → A j → A j)
    (haction : (∀ j x, action j 1 x = x) ∧
      ∀ j g h x, action j (g*h) x = action j g (action j h x))
    (M : ℕ) (f : ∀ j, A j → A (j+1)) (q : A M → B)
    (hequiv : ∀ j, j < M → ∀ g x, f j (action j g x) = action (j+1) g (f j x))
    (hfinal : ∀ g x, q (action M g x) = q x) :
    ∀ g x, q (composeLayers f M (action 0 g x)) = q (composeLayers f M x) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P50

end
