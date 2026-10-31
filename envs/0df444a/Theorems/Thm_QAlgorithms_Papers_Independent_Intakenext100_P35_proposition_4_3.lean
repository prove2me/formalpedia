-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_4_3
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_4_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:20:59.404597+00:00
-- url     : https://prove2.me/theorems/379dc180-1598-4115-9128-0dc383a29063
-- title:
--   Proposition 4.3
-- statement:
--   For $-1<s<\sigma$, $\mathcal D_s\subset\mathcal D_\sigma$. For every $s>0$,
--
--   $$\mathcal B\subset\mathcal D_s.$$
--
--   These inclusions organize the domains of the D-calculus.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 19, Proposition 4.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 4.3, arXiv:2202.03143v1, PDF page(s) 19. -/
theorem proposition_4_3
:
    (∀ s sigma : ℝ, -1 < s → s < sigma → ∀ f, D s f → D sigma f) ∧
    (∀ s : ℝ, 0 < s → ∀ f, BesovClass f → D s f) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
