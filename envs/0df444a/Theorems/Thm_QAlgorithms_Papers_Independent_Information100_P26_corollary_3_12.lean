-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_corollary_3_12
-- name    : QAlgorithms.Papers.Independent.Information100.P26.corollary_3_12
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:24:24.159+00:00
-- url     : https://prove2.me/theorems/37e2f248-5636-4bb9-9ed5-f64736d76b3e
-- title:
--   Corollary 3.12: ETFs yield extreme channels of prescribed rank
-- statement:
--   Let $d\ge1$ and let $(w_k)_{k=1}^N$ be an equiangular tight frame of unit vectors in $\mathbb C^d$, with $N\le2d-2$. Thus the frame is nonempty, $\sum_k|w_k\rangle\langle w_k|=(N/d)I_d$, and distinct vectors have inner-product modulus $\sqrt{(N-d)/(d(N-1))}$. Then
--   $$\tau=\frac dN\sum_k\operatorname{Ad}_{|w_k\rangle\langle w_k|}\in\operatorname{UEBTP}(d),\quad\tau\text{ is extreme},\quad\operatorname{CR}(\tau)=\operatorname{EBR}(\tau)=N.$$
--   The frame identity implies $N\ge d>0$. No ETF existence for arbitrary parameters is asserted, and the orthonormal-basis case $N=d$ is included.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 13, Corollary 3.12

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Corollary 3.12, PDF pp.13. The proof says c>0, but N=d gives c=0; the statement retains this valid boundary case. -/
theorem corollary_3_12 {d n : ℕ} (hd : 0 < d) (w : Fin n → Vec d)
    (hw : ETF w) (hn : n ≤ 2*d-2) :
    let t := frameChannel (fun _ => (d : ℝ)/n) w w
    t ∈ UEBTP d ∧ Extreme t ∧ choiRank t = n ∧ ebRank t = n := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
