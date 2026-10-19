-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P19_separable_polar
-- name    : QAlgorithms.Papers.Independent.Information100.P19.separable_polar
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:39:36.641017+00:00
-- url     : https://prove2.me/theorems/89faba65-ea3e-4487-8aa5-d5170185cd0e
-- title:
--   Abstract / §4.1: separable trace inequalities and their moment polar
-- statement:
--   For every degree $n\ge1$, take all positive finite local dimensions and all unnormalized separable positive operators. Let $M_n^{\rm sep}$ be the closed conic hull of their real tensor-trace evaluation vectors. With the ordinary finite coefficient pairing and the nonnegative polar convention,
--   $$I_n^{\rm sep}=(M_n^{\rm sep})^\circ.$$
--   This identifies precisely the linear inequalities valid for all separable realizations.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, PDF p. 1, Abstract / §4.1: separable trace inequalities and their moment polar

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Abstract / §4.1: separable trace inequalities and their moment polar; arXiv:2609.29471v1, PDF pp.1, 4, 8, 19, 20. -/
theorem separable_polar (n : ℕ) (hn : 1 ≤ n) : sepCone n = tensorPolar (sepMom n) := by sorry

end QAlgorithms.Papers.Independent.Information100.P19

end
