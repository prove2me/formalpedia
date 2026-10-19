-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_corollary_3_5
-- name    : QAlgorithms.Papers.Independent.Information100.P26.corollary_3_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:21:56.729023+00:00
-- url     : https://prove2.me/theorems/ca9cdecc-9f13-4641-9429-afb1567da9e2
-- title:
--   Corollary 3.5: necessary independence, conditional converse, and rank bounds
-- statement:
--   Let $d\ge1$ and $\tau\in\operatorname{UEBTP}(d)$ have a rank-one Kraus decomposition $\tau=\sum_{k=1}^N\operatorname{Ad}_{A_k}$ whose conjugation maps are real-linearly independent. Extremality implies real linear independence of $(A_kA_k^*\oplus A_k^*A_k)_k$. Conversely, that independence implies extremality if every rank-one matrix in $K_\tau$ is a complex scalar multiple of some $A_k$. For every extreme $\tau$ with the specified decomposition,
--   $$N\le2d^2-1,\qquad \operatorname{EBR}(\tau)\le2d^2-1.$$
--   The extra Kraus-space condition applies only to the converse, not to either bound.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 11, Corollary 3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Corollary 3.5, PDF pp.11. -/
theorem corollary_3_5 {d n : ℕ} (hd : 0 < d) (t : Map d) (ht : t ∈ UEBTP d)
    (A : Fin n → Mat d) (hrank : ∀ k, (A k).rank = 1)
    (hdecomp : t = ∑ k, ad (A k))
    (hind : LinearIndependent ℝ (fun k => ad (A k))) :
    (Extreme t → LinearIndependent ℝ (fun k => products (A k))) ∧
    ((∀ B : Mat d, B ∈ krausSpace t → B.rank = 1 →
       ∃ k : Fin n, ∃ c : ℂ, B = c • A k) →
      LinearIndependent ℝ (fun k => products (A k)) → Extreme t) ∧
    (Extreme t → n ≤ 2*d^2-1 ∧ ebRank t ≤ 2*d^2-1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
