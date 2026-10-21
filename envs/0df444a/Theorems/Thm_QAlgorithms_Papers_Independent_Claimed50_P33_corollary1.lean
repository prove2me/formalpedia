-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_corollary1
-- name    : QAlgorithms.Papers.Independent.Claimed50.P33.corollary1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:37:21.118722+00:00
-- url     : https://prove2.me/theorems/92017e5a-2161-4a5d-851e-a22f7136a617
-- title:
--   Corrolary 1: conditional superadditivity inequalities
-- statement:
--   For every normalized state of disjoint finite registers $A,A',B,B',C,C',E$ and for either $F=I_3$ or $F=S_3$,
--
--   $$F(AA':BB':CC'\mid E)\ge F(A:B:C\mid A'B'C'E)+F(A':B':C'\mid E).$$
--
--   All informations are in bits, and the state may correlate primed and unprimed systems arbitrarily. This is conditional superadditivity, retaining the quantum conditioning registers.
-- source:
--   Squashed entanglement for multipartite states and entanglement measures based on the mixed convex roof, arXiv:0704.2236v3, PDF p. 6, Corrolary 1: conditional superadditivity inequalities

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P33

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Corrolary 1 (source spelling), PDF p.6,(42),(43).
There is no product-state hypothesis. -/
theorem corollary1 {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)] (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (hrho : IsDensityMatrix rho) (a ap b bp c cp e : Finset (Fin n))
    (hdis : DisjointRegisters ![a,ap,b,bp,c,cp] e) :
    ∀ kind : InformationKind,
      info kind rho ![a,b,c] (ap ∪ bp ∪ cp ∪ e) +
        info kind rho ![ap,bp,cp] e ≤
      info kind rho ![a ∪ ap,b ∪ bp,c ∪ cp] e := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P33

end
