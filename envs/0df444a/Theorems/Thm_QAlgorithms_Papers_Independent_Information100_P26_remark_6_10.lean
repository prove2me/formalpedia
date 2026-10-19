-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_remark_6_10
-- name    : QAlgorithms.Papers.Independent.Information100.P26.remark_6_10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:57:28.905976+00:00
-- url     : https://prove2.me/theorems/add71bd9-6333-47d4-b053-7322c6afda18
-- title:
--   Remark 6.10: one positive MTD iterate characterizes eventual MTD
-- statement:
--   For every unital quantum channel $\tau$ on $M_d$, $d\ge1$,
--   $$\tau\text{ is eventually MTD}\quad\Longleftrightarrow\quad\exists n_0\ge1:\ \tau^{n_0}\in\operatorname{MTD}(d).$$
--   The forward tail need only start at some later threshold. This does not assert that the very next power after the first MTD power is MTD.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 24, Remark 6.10

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Remark 6.10, PDF pp.24. -/
theorem remark_6_10 {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t) :
    Eventually MTD t ↔ ∃ n0 : ℕ, 1 ≤ n0 ∧ MTD (t^n0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
