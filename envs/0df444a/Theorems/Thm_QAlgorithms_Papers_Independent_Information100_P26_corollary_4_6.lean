-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_corollary_4_6
-- name    : QAlgorithms.Papers.Independent.Information100.P26.corollary_4_6
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:32:01.373064+00:00
-- url     : https://prove2.me/theorems/49675e45-8295-4bf3-b95f-4727dba4fab0
-- title:
--   Corollary 4.6: finite affine span of twisted dephasing channels
-- statement:
--   Every unital quantum channel $\tau$ on $M_d$, $d\ge1$, admits a finite affine decomposition
--   $$\tau=\sum_{j=1}^n a_j\beta_{U_j,V_j},\qquad a_j\in\mathbb R,\quad\sum_j a_j=1,\quad U_j,V_j\in U(d).$$
--   The coefficients may be negative. This places every unital channel in the affine hull of the twisted dephasing family.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 16, Corollary 4.6

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Corollary 4.6, PDF pp.16. -/
theorem corollary_4_6 {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t) :
    ∃ n : ℕ, ∃ a : Fin n → ℝ, ∃ U V : Fin n → Unitary d,
      (∑ j, a j) = 1 ∧ t = ∑ j, a j • beta (U j) (V j) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
