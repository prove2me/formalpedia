-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_theorem_4_14
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.theorem_4_14
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:25:59.73099+00:00
-- url     : https://prove2.me/theorems/4f4ba923-9215-4145-9371-d6da29df3bd2
-- title:
--   Theorem 4.14
-- statement:
--   The span of constants and resolvents $r_\lambda$, $\operatorname{Re}\lambda>0$, is dense in $\mathcal D_s$ for every $s>-1$. However, for $s>0$,
--
--   $$\overline{\mathcal B}^{\|\cdot\|_{\mathcal D_s^\infty}}\ne\mathcal D_s^\infty.$$
--
--   The second assertion uses the stronger bounded-subalgebra norm, not the $\mathcal D_s$ norm.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 23, Theorem 4.14

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Theorem 4.14, arXiv:2202.03143v1, PDF page(s) 23. -/
theorem theorem_4_14
:
    (∀ s : ℝ, -1 < s → ∀ f, D s f →
      NormClosure (ResolventSpan hp hp true) (dSize s) f) ∧
    (∀ s : ℝ, 0 < s → ∃ f, DBounded s f ∧ ¬ NormClosure BesovClass (dBoundedSize s) f) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
