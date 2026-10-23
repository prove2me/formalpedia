-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_lemma_3_7
-- name    : QAlgorithms.Papers.Independent.Information100.P26.lemma_3_7
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:22:33.418381+00:00
-- url     : https://prove2.me/theorems/d3b2477e-195f-4645-8f25-89f694e26208
-- title:
--   Lemma 3.7: rank inequality for sums of outer products
-- statement:
--   Let $d\ge1$ and $X=\sum_{k=1}^s c_k|u_k\rangle\langle v_k|\in M_d$, with every complex coefficient $c_k\ne0$. The vectors may vanish and need not be normalized. Write $r_u=\dim_{\mathbb C}\operatorname{span}\{u_k\}$ and $r_v=\dim_{\mathbb C}\operatorname{span}\{v_k\}$. Then
--   $$r_u+r_v\le s+\operatorname{rank}X.$$
--   This addition-only form avoids natural-number truncation and includes the empty decomposition.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 11, Lemma 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Lemma 3.7, PDF pp.11. -/
theorem lemma_3_7 {d s : ℕ} (hd : 0 < d) (X : Mat d)
    (c : Fin s → ℂ) (u v : Fin s → Vec d) (hc : ∀ k, c k ≠ 0)
    (hX : X = ∑ k, c k • outer (u k) (v k)) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range u)) +
      Module.finrank ℂ (Submodule.span ℂ (Set.range v)) ≤ s + X.rank := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
