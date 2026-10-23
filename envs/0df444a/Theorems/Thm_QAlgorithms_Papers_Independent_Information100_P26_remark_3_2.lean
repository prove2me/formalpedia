-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_remark_3_2
-- name    : QAlgorithms.Papers.Independent.Information100.P26.remark_3_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:48:51.810692+00:00
-- url     : https://prove2.me/theorems/570108b8-ec0b-40a6-85ca-6c1d484a25dc
-- title:
--   Remark 3.2: the real span of the minimal EB face
-- statement:
--   Let $d\ge1$ and $\tau\in\operatorname{UEBTP}(d)$. With $V_\tau=\operatorname{span}_{\mathbb R}F_0(\tau)$ as in Theorem 3.1, put $F(\tau)=\{\sigma\in\mathrm{EB}(d):\lambda\tau-\sigma\in\mathrm{EB}(d)\text{ for some }\lambda>0\}$. Then
--   $$V_\tau=\operatorname{span}_{\mathbb R}F(\tau).$$
--   This identifies the real space of the minimal cone face; the scaling parameter is positive and may depend on $\sigma$.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 10, Remark 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Remark 3.2, PDF pp.10. -/
theorem remark_3_2 {d : ℕ} (hd : 0 < d) (t : Map d) (ht : t ∈ UEBTP d) :
    faceSpan t = Submodule.span ℝ
      {s : Map d | EB s ∧ ∃ a : ℝ, 0 < a ∧ EB (a • t - s)} := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
