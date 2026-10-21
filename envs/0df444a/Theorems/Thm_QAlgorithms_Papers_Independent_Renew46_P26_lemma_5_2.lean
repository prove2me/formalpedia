-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_lemma_5_2
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.lemma_5_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:58:47.930299+00:00
-- url     : https://prove2.me/theorems/b015e171-60dd-468d-8055-5a6d7b63b727
-- title:
--   Lemma 5.2
-- statement:
--   Let $\alpha=(a_1,\ldots,a_n)\in\mathbb C^n$. If $1\leq i\leq n-2$ and the consecutive fragment at positions $i,i+1,i+2$ is $(a,a+1,a)$, then
--
--   $$\alpha\notin\operatorname{Spec}(n).$$
--
--   The spectrum is defined through actual irreducible representations. The valid index range excludes empty or truncated fragments.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 18, Lemma 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Lemma 5.2 (PDF p.18). The three indices are genuine valid positions. -/
theorem lemma_5_2 {n : ℕ} (alpha : Fin n → ℂ) (i : ℕ) (hi : i + 2 < n)
    (hfirst : alpha ⟨i, by omega⟩ = alpha ⟨i + 2, hi⟩)
    (hnext : alpha ⟨i + 1, by omega⟩ = alpha ⟨i, by omega⟩ + 1) :
    alpha ∉ spectrum n := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
