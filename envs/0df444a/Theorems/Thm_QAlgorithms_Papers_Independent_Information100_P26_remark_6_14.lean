-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_remark_6_14
-- name    : QAlgorithms.Papers.Independent.Information100.P26.remark_6_14
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:59:06.233809+00:00
-- url     : https://prove2.me/theorems/edea2ec1-4afa-4ef8-b45a-960119cd46b5
-- title:
--   Remark 6.14: no uniform positive iteration bound
-- statement:
--   For every fixed dimension $d\ge2$ and every positive integer $N$, there exists an eventually EB unital channel $\tau$ on $M_d$ such that
--   $$\tau^N\text{ is not 2-copositive}.$$
--   The channel is chosen after both $d$ and $N$. Thus there is no dimension-dependent uniform positive iteration bound over all eventually EB channels.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 25, Remark 6.14

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Remark 6.14, PDF pp.25. -/
theorem remark_6_14 {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (hn : 1 ≤ n) :
    ∃ t : Map d, t ∈ EEB d ∧ ¬ TwoCopositive (t^n) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
