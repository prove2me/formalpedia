-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_corollary_6_15
-- name    : QAlgorithms.Papers.Independent.Information100.P26.corollary_6_15
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:46:09.58828+00:00
-- url     : https://prove2.me/theorems/3ccc1138-cbac-46b5-9d33-64e15e8022ae
-- title:
--   Corollary 6.15: primitive unital channels are eventually MTD
-- statement:
--   Every unital primitive channel $\tau$ on $M_d$, $d\ge1$, satisfies
--   $$\tau\text{ is eventually MTD}.$$
--   For unital channels, the source characterizes discrete primitivity by $\mathcal P(\tau)=\mathbb C I_d$. Eventual MTD is asserted at all sufficiently large positive powers, without a uniform bound.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 25, Corollary 6.15

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Corollary 6.15, PDF pp.25. -/
theorem corollary_6_15 {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t)
    (hprim : Primitive t) : Eventually MTD t := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
