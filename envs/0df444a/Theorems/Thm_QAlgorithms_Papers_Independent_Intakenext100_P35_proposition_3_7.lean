-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_proposition_3_7
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.proposition_3_7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:14:57.074135+00:00
-- url     : https://prove2.me/theorems/65f15e10-7412-4e60-9dc2-9a3de9192dd2
-- title:
--   Proposition 3.7
-- statement:
--   Let $\mathcal R_0(\mathbb C_+)$ be the complex linear span of $(\lambda+z)^{-1}$ for $\operatorname{Re}\lambda>0$. Relative to the ambient space $\mathcal B$,
--
--   $$\overline{\mathcal R_0}^{\|\cdot\|_{\mathcal B}}=\overline{\mathcal R_0}^{\|\cdot\|_\infty}=\mathcal B\cap C_0(\overline{\mathbb C_+}).$$
--
--   This identifies the vanishing subalgebra in both approximation topologies.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 9, Proposition 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Proposition 3.7, arXiv:2202.03143v1, PDF page(s) 9. -/
theorem proposition_3_7
(f : AnalyticSymbol) (hf : BesovClass f) :
    (NormClosure (ResolventSpan hp hp false) bSize f ↔ Vanishes f) ∧
    (NormClosure (ResolventSpan hp hp false) (supSize hp) f ↔ Vanishes f) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
