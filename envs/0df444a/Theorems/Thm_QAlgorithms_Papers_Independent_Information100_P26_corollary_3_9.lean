-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_corollary_3_9
-- name    : QAlgorithms.Papers.Independent.Information100.P26.corollary_3_9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:23:52.889796+00:00
-- url     : https://prove2.me/theorems/271c1243-fa25-49dd-8930-a1febf5a7f9c
-- title:
--   Corollary 3.9: exactly the twisted channels are extreme in dimension two
-- statement:
--   For a complex-linear map $\tau$ on $M_2$,
--   $$\tau\text{ is an extreme point of }\operatorname{UEBTP}(2)\quad\Longleftrightarrow\quad\tau\text{ is twisted dephasing}.$$
--   Both membership and extremality on the left are part of the assertion.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 12, Corollary 3.9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Corollary 3.9, PDF pp.12. -/
theorem corollary_3_9 (t : Map 2) : Extreme t ↔ Twisted t := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
