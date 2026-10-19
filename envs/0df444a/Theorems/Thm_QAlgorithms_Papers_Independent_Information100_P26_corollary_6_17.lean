-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_corollary_6_17
-- name    : QAlgorithms.Papers.Independent.Information100.P26.corollary_6_17
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:46:43.338731+00:00
-- url     : https://prove2.me/theorems/332e6a4f-9a68-4840-9fd9-73574d0096de
-- title:
--   Corollary 6.17: unital 2-copositive channels are eventually MTD
-- statement:
--   For every unital 2-copositive quantum channel $\tau$ on $M_d$, $d\ge1$,
--   $$\tau^n\in\operatorname{MTD}(d)\quad\text{for all sufficiently large }n.$$
--   Only 2-copositivity is needed; no PPT assumption is added. The iteration threshold may depend on the channel.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 26, Corollary 6.17

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Corollary 6.17, PDF pp.26. -/
theorem corollary_6_17 {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t)
    (hcop : TwoCopositive t) : Eventually MTD t := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
