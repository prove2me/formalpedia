-- Prove2me | Theorems.Thm_SupportVectorMachines_LossFunctions_lemma_2_30_pointwise_inequality
-- name    : SupportVectorMachines.LossFunctions.lemma_2_30_pointwise_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T21:21:22.602853+00:00
-- url     : https://prove2.me/theorems/db233de4-6ed8-4410-846b-ea7501632d16
-- title:
--   Lemma 2.30 — a pointwise inequality relating $\eta$ and a clipped prediction
-- statement:
--   This is Lemma 2.30 of Steinwart & Christmann, *Support Vector Machines* (Springer 2008,
--   p. 36, Eq. (2.15)), the elementary pointwise inequality Theorem 2.31's proof invokes directly.
--
--   For all $\eta \in [0,1]$ and all $t \in [-1,1]$,
--   $$
--   |2\eta-1| \cdot \mathbf 1_{(-\infty,0]}\big((2\eta-1)\cdot\operatorname{sgn} t\big) \;\le\; |2\eta-1|\cdot\big|t-\operatorname{sgn}(2\eta-1)\big|,
--   $$
--   where $\operatorname{sgn}$ is the book's own sign convention ($\operatorname{sgn}(0):=1$,
--   p. 36).
--
--   The left-hand side is exactly the pointwise integrand of the excess classification risk
--   $R_{L_{\mathrm{class}},P}(f) - R^*_{L_{\mathrm{class}},P}$ once expanded in terms of $\eta$
--   (see Example 2.4); the right-hand side is the pointwise integrand of the excess hinge risk
--   given by the first assertion of Theorem 2.31. The lemma is the one purely pointwise,
--   measure-free step needed to pass from one integrand to the other.
--
--   **Formalization Note** The indicator $\mathbf 1_{(-\infty,0]}(\cdot)$ is written as
--   `if (2*η-1)*sgn t ≤ 0 then |2*η-1| else 0`, matching the left-hand side's product with
--   $|2\eta-1|$ exactly rather than introducing a separate indicator-times-constant pattern.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 36, Lemma 2.30, Eq. (2.15)

import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_ClassificationLosses

namespace SupportVectorMachines.LossFunctions

/-- Lemma 2.30, p. 36, Eq. (2.15): for all `η ∈ [0,1]` and all `t ∈ [-1,1]`,
`|2η - 1| · 1_{(-∞,0]}((2η - 1) · sign t) ≤ |2η - 1| · |t - sign(2η - 1)|`. -/
theorem lemma_2_30_pointwise_inequality (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) 1) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (if (2 * η - 1) * sgn t ≤ 0 then |2 * η - 1| else 0) ≤
      |2 * η - 1| * |t - sgn (2 * η - 1)| := by sorry

end SupportVectorMachines.LossFunctions
