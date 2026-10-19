-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_theorem_4_7
-- name    : QAlgorithms.Papers.Independent.Information100.P26.theorem_4_7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:32:49.022214+00:00
-- url     : https://prove2.me/theorems/745d44b4-a067-4cae-97ae-1ea5646a49ef
-- title:
--   Theorem 4.7: an MTD neighborhood of the completely depolarizing channel
-- statement:
--   For each $d\ge1$ there is $\varepsilon>0$, depending only on $d$, such that every unital quantum channel $\tau$ satisfies
--   $$\|\tau-\delta_d\|_{\rm HS}<\varepsilon\quad\Longrightarrow\quad\tau\in\operatorname{MTD}(d).$$
--   This is a relative neighborhood among unital channels; the radius is chosen before the channel. The source leaves the norm unspecified, so the equivalent finite-dimensional Hilbert–Schmidt norm is used.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 16, Theorem 4.7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Theorem 4.7, PDF pp.16. -/
theorem theorem_4_7 {d : ℕ} (hd : 0 < d) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : Map d, UnitalChannel t →
      hsNorm (t - depolarizing d) < e → MTD t := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
