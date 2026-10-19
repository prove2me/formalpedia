-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_corollary_3_8
-- name    : QAlgorithms.Papers.Independent.Information100.P26.corollary_3_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:23:16.846511+00:00
-- url     : https://prove2.me/theorems/48514bd7-15d3-4f31-861b-71df7888d580
-- title:
--   Corollary 3.8: full-spark frame channels and twisted-channel extremality
-- statement:
--   Fix $d\ge1$. Let $d\le N\le2d-2$, let $u_k,v_k\in\mathbb C^d$ be unit vectors and let $p_k>0$. Assume both weighted resolutions $\sum_kp_k|u_k\rangle\langle u_k|=\sum_kp_k|v_k\rangle\langle v_k|=I_d$, every indexed $d$-element subfamily of each vector family is complex-linearly independent, and the pairs $(|u_k\rangle\langle u_k|,|v_k\rangle\langle v_k|)$ are real-linearly independent. Then
--   $$\tau=\sum_kp_k\operatorname{Ad}_{|u_k\rangle\langle v_k|}\in\operatorname{UEBTP}(d),\quad \tau\text{ is extreme},\quad\operatorname{CR}(\tau)=\operatorname{EBR}(\tau)=N.$$
--   In addition, every twisted dephasing channel in every positive dimension is extreme. This last clause includes $d=1$, independently of the frame-size restriction.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 11, Corollary 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Corollary 3.8, PDF pp.11,12. -/
theorem corollary_3_8 {d : ℕ} (hd : 0 < d) :
    (∀ (n : ℕ) (p : Fin n → ℝ) (u v : Fin n → Vec d),
      d ≤ n → n ≤ 2*d-2 →
      (∀ k, QAlgorithms.RealRegisters.IsUnitVector (WithLp.toLp 2 (u k)) ∧
        QAlgorithms.RealRegisters.IsUnitVector (WithLp.toLp 2 (v k)) ∧ 0 < p k) →
      (∑ k, p k • outer (u k) (u k)) = (1 : Mat d) →
      (∑ k, p k • outer (v k) (v k)) = (1 : Mat d) →
      FullSpark u → FullSpark v →
      LinearIndependent ℝ (fun k => (outer (u k) (u k), outer (v k) (v k))) →
      frameChannel p u v ∈ UEBTP d ∧ Extreme (frameChannel p u v) ∧
        choiRank (frameChannel p u v) = n ∧ ebRank (frameChannel p u v) = n) ∧
    (∀ t : Map d, Twisted t → Extreme t) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
