-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_theorem_5_1
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.theorem_5_1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:56:32.152489+00:00
-- url     : https://prove2.me/theorems/e3455402-be58-4670-9eee-e4a431daabeb
-- title:
--   Theorem 5.1
-- statement:
--   Define $\operatorname{Spec}(n)$ from joint eigenvectors in actual irreducible modules. Independently, let $\operatorname{Cont}(n)$ consist of integer vectors $\alpha=(a_1,\ldots,a_n)$ with $a_1=0$, every later entry having a neighboring integer among preceding entries, and both $a-1$ and $a+1$ occurring between any two occurrences of $a$. Then
--
--   $$\operatorname{Spec}(n)\subseteq\operatorname{Cont}(n).$$
--
--   For $n=0$ the content conditions are vacuous. This is a substantive spectral restriction rather than a definition of the spectrum.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 17, Theorem 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 5.1 (PDF pp.17–19). Actual spectral weights satisfy all three
independently defined content conditions, including integrality. -/
theorem theorem_5_1 (n : ℕ) : spectrum n ⊆ contentVectors n := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
