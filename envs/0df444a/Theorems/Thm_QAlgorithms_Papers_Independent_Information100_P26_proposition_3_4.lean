-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_proposition_3_4
-- name    : QAlgorithms.Papers.Independent.Information100.P26.proposition_3_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:21:04.232981+00:00
-- url     : https://prove2.me/theorems/fd5e8b7b-2f8d-408b-b3a7-ec72dea12294
-- title:
--   Proposition 3.4: an independent rank-one conjugation decomposition
-- statement:
--   For $d\ge1$, every entanglement-breaking linear map $\tau$ on $M_d$ admits a finite decomposition
--   $$\tau=\sum_{k=1}^{N}\operatorname{Ad}_{A_k}$$
--   with every $A_k$ rank one and $(\operatorname{Ad}_{A_k})_k$ linearly independent over $\mathbb R$. The empty sum $N=0$ is permitted for the zero map. Trace preservation is not required. This is an independent generating decomposition for the EB cone.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 10, Proposition 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Proposition 3.4, PDF pp.10. -/
theorem proposition_3_4 {d : ℕ} (hd : 0 < d) (t : Map d) (ht : EB t) :
    ∃ n : ℕ, ∃ A : Fin n → Mat d,
      (∀ k, (A k).rank = 1) ∧ t = ∑ k, ad (A k) ∧
      LinearIndependent ℝ (fun k => ad (A k)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
