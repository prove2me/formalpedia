-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_proposition_6_4
-- name    : QAlgorithms.Papers.Independent.Information100.P26.proposition_6_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:44:33.912508+00:00
-- url     : https://prove2.me/theorems/d316aed9-1e7b-4ab5-b2f2-bed2cd6bbdd2
-- title:
--   Proposition 6.4: the peripheral space is a commutative C-star algebra
-- statement:
--   For every unital 2-copositive quantum channel $\tau$ on $M_d$, $d\ge1$,
--   $$\mathcal P(\tau)\text{ is a commutative unital }C^*\text{-subalgebra of }M_d.$$
--   The multiplication and adjoint are inherited from $M_d$. Both algebra closure and pairwise commutation are retained, not merely a statement about a modified product.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 22, Proposition 6.4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Proposition 6.4, PDF pp.22,23. -/
theorem proposition_6_4 {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t)
    (hcop : TwoCopositive t) : CStar (peripheral t) ∧ Commutative (peripheral t) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
