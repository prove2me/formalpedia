-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_example_3_10
-- name    : QAlgorithms.Papers.Independent.Information100.P26.example_3_10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:54:11.422773+00:00
-- url     : https://prove2.me/theorems/c5530f74-10fb-44be-85e7-70b1a1e5e083
-- title:
--   Example 3.10: explicit harmonic-frame extreme channels
-- statement:
--   Let $d\ge1$ and $d\le N\le2d-2$. Put $\zeta=e^{2\pi i/N}$ and $w_k=d^{-1/2}(1,\zeta^k,\ldots,\zeta^{(d-1)k})^T$ for $1\le k\le N$. The vectors are unit, their projectors are real-linearly independent, every indexed $d$-element subfamily is complex-linearly independent, and $\sum_k|w_k\rangle\langle w_k|=(N/d)I_d$. Thus
--   $$\tau=\frac dN\sum_k\operatorname{Ad}_{|w_k\rangle\langle w_k|}\in\operatorname{UEBTP}(d),\quad\tau\text{ is extreme},\quad\operatorname{CR}(\tau)=\operatorname{EBR}(\tau)=N.$$
--   This is a concrete construction for every integer in the stated size interval. The formal index $k\in\mathrm{Fin}(N)$ uses source exponent $k+1$.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 12, Example 3.10

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Example 3.10, PDF pp.12. -/
theorem example_3_10 {d n : ℕ} (hd : 0 < d) (hlo : d ≤ n) (hhi : n ≤ 2*d-2) :
    let w : Fin n → Vec d := harmonic
    let t := frameChannel (fun _ => (d : ℝ)/n) w w
    (∀ k, QAlgorithms.RealRegisters.IsUnitVector (WithLp.toLp 2 (w k))) ∧
    (∑ k, outer (w k) (w k)) = ((n : ℝ)/d) • (1 : Mat d) ∧
    FullSpark w ∧ LinearIndependent ℝ (fun k => outer (w k) (w k)) ∧
    t ∈ UEBTP d ∧ Extreme t ∧ choiRank t = n ∧ ebRank t = n := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
