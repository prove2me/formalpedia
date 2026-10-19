-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_remark_3_13
-- name    : QAlgorithms.Papers.Independent.Information100.P26.remark_3_13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:54:45.431139+00:00
-- url     : https://prove2.me/theorems/4427563b-6e19-4173-b182-ec3ffbdf5c6d
-- title:
--   Remark 3.13: MTD is properly contained in unital EB for every d at least three
-- statement:
--   For $d\ge3$ and $d<N\le2d-2$, the harmonic-frame channels of Example 3.10 and any ETF channels of Corollary 3.12 are not twisted dephasing. Their Choi and EB ranks equal $N>d$, whereas every twisted dephasing channel has both ranks exactly $d$. In particular,
--   $$\operatorname{MTD}(d)\subsetneq\operatorname{UEBTP}(d)\qquad(d\ge3).$$
--   The harmonic construction with $N=d+1$ witnesses every dimension; no general ETF existence assumption is used.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 13, Remark 3.13

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Remark 3.13, PDF pp.13. -/
theorem remark_3_13 {d : ℕ} (hd : 3 ≤ d) :
    (∀ n : ℕ, d < n → n ≤ 2*d-2 →
      ¬ Twisted (frameChannel (fun _ : Fin n => (d : ℝ)/n)
        (harmonic : Fin n → Vec d) harmonic)) ∧
    (∀ (n : ℕ) (w : Fin n → Vec d), d < n → n ≤ 2*d-2 → ETF w →
      ¬ Twisted (frameChannel (fun _ => (d : ℝ)/n) w w)) ∧
    (∀ t : Map d, Twisted t → choiRank t = d ∧ ebRank t = d) ∧
    ({t : Map d | MTD t} ⊂ UEBTP d) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
