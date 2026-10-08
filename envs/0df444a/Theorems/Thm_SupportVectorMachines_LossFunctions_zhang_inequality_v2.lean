-- Prove2me | Theorems.Thm_SupportVectorMachines_LossFunctions_zhang_inequality_v2
-- name    : SupportVectorMachines.LossFunctions.zhang_inequality_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:31.501757+00:00
-- url     : https://prove2.me/theorems/8e617f61-725d-4071-a93b-e88151615585
-- title:
--   Zhang's inequality relating the hinge risk and the classification risk (measurable $\eta$, $[0,\infty]$-valued risks)
-- statement:
--   This is Theorem 2.31 (Zhang's inequality) of Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 37).
--
--   Let $P$ be a distribution on $X \times Y$ with $Y := \{-1,1\}$, let $\eta(x) := P(y = 1 \mid x)$ be the conditional probability of the positive label, and $f^*_{L_{\mathrm{class}},P}(x) := \operatorname{sign}(2\eta(x) - 1)$ the Bayes classification function ($\operatorname{sign}(0) := 1$). Then:
--
--   1. For every measurable $f : X \to [-1,1]$,
--   $$
--   R_{L_{\mathrm{hinge}},P}(f) - R^*_{L_{\mathrm{hinge}},P} = \int_X \big|f(x) - f^*_{L_{\mathrm{class}},P}(x)\big|\,|2\eta(x) - 1|\,dP_X(x),
--   $$
--   an exact equality (both sides finite), where $P_X$ is the $X$-marginal of $P$.
--   2. For every measurable $f : X \to \mathbb R$,
--   $$
--   R_{L_{\mathrm{class}},P}(f) - R^*_{L_{\mathrm{class}},P} \le R_{L_{\mathrm{hinge}},P}(f) - R^*_{L_{\mathrm{hinge}},P}.
--   $$
--
--   **Formalization Note.** The retired version pinned $\eta$ only by a real-valued Bochner-integral identity, without requiring $\eta$ to be measurable or $[0,1]$-valued, so a non-measurable $\eta$ satisfied it vacuously (junk integral $0$) and the identity in 1 failed; it also restricted 2 to functions of finite hinge risk. The corrected statement: $\eta$ is a measurable $[0,1]$-valued version of the regular conditional probability, pinned by $P(A \times \{1\}) = \int_A \eta\,dP_X$ for every measurable $A$ (every version satisfies the theorem, as both sides are invariant under $P_X$-null changes of $\eta$); $Y = \{-1,1\}$ is the hypothesis $P(X \times \{-1,1\}) = 1$ (labels embedded in $\mathbb R$); the loss is the bundled measurable nonnegative `Loss X` of Definition 2.1 (instantiated by the hinge and classification losses); risks are $[0,\infty]$-valued Lebesgue integrals and the Bayes risks infima in $[0,\infty]$, so 2 holds for every measurable $f$ (an infinite hinge risk makes the right-hand side $\infty$), and the differences are exact since $R \ge R^*$. The integral in 1 is written as a Lebesgue integral of the nonnegative integrand.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 37, Theorem 2.31 (Zhang's inequality)

import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_RiskBasics_v2
import Definitions.Def_SupportVectorMachines_LossFunctions_ClassificationLosses_v2

open MeasureTheory

namespace SupportVectorMachines.LossFunctions

/-- Theorem 2.31 (Zhang's inequality), Steinwart & Christmann, *Support Vector Machines*,
Springer 2008, p. 37: given a distribution `P` on `X × Y` (`Y := {-1,1}`, i.e. `P` is supported
on `X × {-1,1}`) with `η(x) := P(y=1|x)` (a measurable `[0,1]`-valued version of the regular
conditional probability, pinned by `P(A × {1}) = ∫_A η dP_X` for every measurable `A`) and Bayes
classifier `f*_{L_class,P}(x) := sign(2η(x)-1)`:

* for every measurable `f : X → [-1,1]`,
  `R_{L_hinge,P}(f) - R*_{L_hinge,P} = ∫_X |f(x) - f*_{L_class,P}(x)| · |2η(x) - 1| dP_X(x)`
  (an exact equality; both sides are finite);
* for every measurable `f : X → ℝ`,
  `R_{L_class,P}(f) - R*_{L_class,P} ≤ R_{L_hinge,P}(f) - R*_{L_hinge,P}`,
  where risks are `[0,∞]`-valued (an infinite hinge risk makes the right-hand side `∞`).

Corrected version of `zhang_inequality`, which did not require `η` to be measurable or
`[0,1]`-valued (so a non-measurable `η` satisfied its Bochner-integral defining identity
vacuously) and which restricted the second assertion to functions with finite hinge risk. -/
theorem zhang_inequality_v2 {X : Type*} [MeasurableSpace X] (P : Measure (X × ℝ))
    [IsProbabilityMeasure P] (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) (η : X → ℝ)
    (hη_meas : Measurable η) (hη01 : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (hη : ∀ A, MeasurableSet A →
      P (A ×ˢ ({1} : Set ℝ)) = ∫⁻ x in A, ENNReal.ofReal (η x) ∂(P.map Prod.fst)) :
    (∀ f : X → ℝ, Measurable f → (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) →
        risk hingeLoss P f - bayesRisk hingeLoss P =
          ∫⁻ x, ENNReal.ofReal (|f x - bayesClassifier η x| * |2 * η x - 1|)
            ∂(P.map Prod.fst)) ∧
      ∀ f : X → ℝ, Measurable f →
        risk classLoss P f - bayesRisk classLoss P ≤
          risk hingeLoss P f - bayesRisk hingeLoss P := by sorry

end SupportVectorMachines.LossFunctions
