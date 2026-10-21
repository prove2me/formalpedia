-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_corollary_5_5
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.corollary_5_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:02:07.943517+00:00
-- url     : https://prove2.me/theorems/c9270b4a-70a4-47b0-8225-4b8450cb81cc
-- title:
--   Corollary 5.5
-- statement:
--   Let $\alpha\in\operatorname{Spec}(n)$ and $\beta\in\operatorname{Cont}(n)$. If $\beta$ is reachable from $\alpha$ by a finite sequence of admissible adjacent swaps, then
--
--   $$\beta\in\operatorname{Spec}(n),\qquad\alpha\sim\beta.$$
--
--   The relation $\sim$ denotes occurrence in the same actual irreducible representation. Both spectral occurrence and preservation of the irreducible class are conclusions.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 21, Corollary 5.5

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Corollary 5.5 (PDF p.21), including occurrence in the same irreducible. -/
theorem corollary_5_5 {n : ℕ} (alpha beta : Fin n → ℂ)
    (ha : alpha ∈ spectrum n) (hb : beta ∈ contentVectors n)
    (hab : AdmissiblyEquivalent alpha beta) :
    beta ∈ spectrum n ∧ SameIrreducible alpha beta := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
