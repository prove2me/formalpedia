-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_corollary_3_3
-- name    : QAlgorithms.Papers.Independent.Information100.P26.corollary_3_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:20:04.663234+00:00
-- url     : https://prove2.me/theorems/19cb74a9-20bd-4dd9-b1da-09be8eb0704c
-- title:
--   Corollary 3.3: a sufficient Kraus-space basis criterion for extremality
-- statement:
--   Let $\tau\in\operatorname{UEBTP}(d)$, $d\ge1$, and let $K_\tau$ be its Kraus operator space. Define $W_\tau=\operatorname{span}_{\mathbb R}\{\operatorname{Ad}_B:B\in K_\tau,\operatorname{rank}B=1\}$. If $W_\tau$ has a finite basis $(\operatorname{Ad}_{B_k})_{k=1}^m$ with every $B_k$ rank one and $(B_kB_k^*\oplus B_k^*B_k)_k$ real-linearly independent, then
--   $$\tau\text{ is extreme in }\operatorname{UEBTP}(d).$$
--   The criterion is sufficient; no converse is claimed.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 10, Corollary 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Corollary 3.3, PDF pp.10. -/
theorem corollary_3_3 {d m : ℕ} (hd : 0 < d) (t : Map d) (ht : t ∈ UEBTP d)
    (B : Fin m → Mat d) (hrank : ∀ k, (B k).rank = 1)
    (hbasis : IsRealBasis (fun k => ad (B k)) (krausRankOneSpan t))
    (hind : LinearIndependent ℝ (fun k => products (B k))) : Extreme t := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
