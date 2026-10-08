-- Prove2me | Theorems.Thm_SupportVectorMachines_Classification_theorem_2_31_instance_zhang_v2
-- name    : SupportVectorMachines.Classification.theorem_2_31_instance_zhang_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:14.025061+00:00
-- url     : https://prove2.me/theorems/015abad0-9827-43b7-afd3-b19eadf46a1f
-- title:
--   Theorem 2.31 instance — excess classification risk bounded by excess hinge risk ($Y = \{-1,1\}$)
-- statement:
--   This is the instance of Theorem 2.31 (Zhang's inequality) of Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 37) used in the proof of Theorem 8.1 (p. 289).
--
--   Let $P$ be a distribution on $X \times Y$ with $Y := \{-1,1\}$ (binary classification). For every measurable $f : X \to \mathbb R$,
--   $$
--   R_{L_{\mathrm{class}},P}(f) - R^*_{L_{\mathrm{class}},P} \le R_{L_{\mathrm{hinge}},P}(f) - R^*_{L_{\mathrm{hinge}},P}.
--   $$
--
--   Only the inequality (second) clause of Theorem 2.31 is restated, since it is what Theorem 8.1's proof uses; the series' `01-loss-functions` mission contains the full theorem.
--
--   **Formalization Note.** The retired version let $P$ be any probability measure on $X \times \mathbb R$; with a label $y = 4$ the hinge loss rewards the wrong sign and the inequality fails (the accepted disproof). The corrected statement adds the chapter's standing convention $Y = \{-1,1\}$ as $P(X \times \{-1,1\}) = 1$ (labels embedded in $\mathbb R$). Risks are $[0,\infty]$-valued Lebesgue integrals of the bundled measurable nonnegative losses of Definition 2.1, and the Bayes risks are infima in $[0,\infty]$, so the retired integrability hypotheses on $f$ are no longer needed (an infinite hinge risk makes the right-hand side $\infty$, as in the book) and the differences are exact since $R \ge R^*$.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 37, Theorem 2.31 (second assertion, instantiated as in the proof of Theorem 8.1, p. 289)

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics_v2
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses_v2

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- The instance of Theorem 2.31 (Zhang's inequality), Steinwart & Christmann, *Support Vector
Machines*, Springer 2008, p. 37, used inside the proof of Theorem 8.1 (p. 289): for a
distribution `P` on `X × Y` with `Y := {-1,1}` (binary classification, the standing convention of
Chapter 8: `P` is supported on `X × {-1,1}`) and every measurable `f : X → ℝ`, the excess
classification risk is bounded by the excess (unrestricted) hinge risk,
`R_{L_class,P}(f) - R*_{L_class,P} ≤ R_{L_hinge,P}(f) - R*_{L_hinge,P}`, risks being
`[0,∞]`-valued (an infinite hinge risk makes the right-hand side `∞`). This is the chapter's own
formalization series's `01-loss-functions` mission's `zhang_inequality`, second clause, restated
locally per Hard Rule 9 rather than imported.
Corrected version of `theorem_2_31_instance_zhang`, which allowed arbitrary real labels (for
which Zhang's inequality is false) and restricted `f` to finite hinge risk. -/
theorem theorem_2_31_instance_zhang_v2 {X : Type*} [MeasurableSpace X] (P : Measure (X × ℝ))
    [IsProbabilityMeasure P] (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1)
    (f : X → ℝ) (hf : Measurable f) :
    risk classLoss P f - bayesRisk classLoss P ≤
      risk hingeLoss P f - bayesRisk hingeLoss P := by sorry

end SupportVectorMachines.Classification
