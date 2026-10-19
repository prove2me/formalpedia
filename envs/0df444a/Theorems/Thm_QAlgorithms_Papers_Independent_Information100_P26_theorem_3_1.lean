-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_theorem_3_1
-- name    : QAlgorithms.Papers.Independent.Information100.P26.theorem_3_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:19:05.520976+00:00
-- url     : https://prove2.me/theorems/a1f16ec1-c50c-4f7a-a2dd-cead01ed7662
-- title:
--   Theorem 3.1: extremality through a basis of the EB face span
-- statement:
--   Let $\tau\in\operatorname{UEBTP}(d)$, where $d\ge1$. Put $F_0(\tau)=\{\operatorname{Ad}_B:\operatorname{rank}B=1,\ \tau-\operatorname{Ad}_B\text{ is EB}\}$ and $V_\tau=\operatorname{span}_{\mathbb R}F_0(\tau)$. For any finite basis $(\operatorname{Ad}_{B_k})_{k=1}^n$ of $V_\tau$ selected from $F_0(\tau)$,
--   $$\tau\text{ is extreme in }\operatorname{UEBTP}(d)\quad\Longleftrightarrow\quad (B_kB_k^*\oplus B_k^*B_k)_{k=1}^n\text{ is linearly independent over }\mathbb R.$$
--   Here $\operatorname{Ad}_B(X)=BXB^*$. This criterion uses the whole face span, rather than an arbitrary Kraus representation.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 9, Theorem 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Theorem 3.1, PDF pp.9,10. -/
theorem theorem_3_1 {d n : ℕ} (hd : 0 < d) (t : Map d) (ht : t ∈ UEBTP d)
    (B : Fin n → Mat d)
    (hB : ∀ k, (B k).rank = 1 ∧ EB (t - ad (B k)))
    (hbasis : IsRealBasis (fun k => ad (B k)) (faceSpan t)) :
    Extreme t ↔ LinearIndependent ℝ (fun k => products (B k)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
