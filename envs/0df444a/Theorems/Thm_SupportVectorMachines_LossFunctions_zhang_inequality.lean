-- Prove2me | Theorems.Thm_SupportVectorMachines_LossFunctions_zhang_inequality
-- name    : SupportVectorMachines.LossFunctions.zhang_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:23:32.562988+00:00
-- url     : https://prove2.me/theorems/bb91dcf0-aee8-4ace-bdba-ff5f9e6eb618
-- title:
--   Zhang's inequality relating the hinge risk and the classification risk
-- statement:
--   This is Theorem 2.31 (Zhang's inequality) of Steinwart & Christmann, *Support Vector
--   Machines* (Springer 2008, p. 37), the book's sharpest calibration result relating a convex
--   surrogate loss to the classification loss it stands in for.
--
--   Let $P$ be a distribution on $X \times Y$ with $Y := \{-1,1\}$, and write
--   $\eta(x) := P(y=1 \mid x)$ for the conditional probability of the positive label, and
--   $f^*_{L_{\mathrm{class}},P}(x) := \operatorname{sgn}(2\eta(x)-1)$ for the associated Bayes
--   classification function ($\operatorname{sgn}(0):=1$). Then:
--
--   1. For every measurable $f : X \to [-1,1]$ with finite hinge risk,
--      $$
--      R_{L_{\mathrm{hinge}},P}(f) - R^*_{L_{\mathrm{hinge}},P} = \int_X \big|f(x) - f^*_{L_{\mathrm{class}},P}(x)\big| \cdot |2\eta(x)-1| \, dP_X(x),
--      $$
--      an **exact equality**, where $P_X$ is the $X$-marginal of $P$.
--   2. For every measurable $f : X \to \mathbb R$ with finite hinge and classification risk,
--      $$
--      R_{L_{\mathrm{class}},P}(f) - R^*_{L_{\mathrm{class}},P} \;\le\; R_{L_{\mathrm{hinge}},P}(f) - R^*_{L_{\mathrm{hinge}},P}.
--      $$
--
--   The first assertion identifies the excess hinge risk with a weighted $L^1$-distance to the
--   Bayes classifier; the second shows that making the (convex, tractable) excess hinge risk
--   small is always at least as hard as making the excess classification risk small, which is
--   exactly what makes the hinge loss a valid surrogate for classification.
--
--   **Formalization Note** $\eta$ is represented via its defining disintegration property: for
--   every measurable $A \subseteq X$, $P(A \times \{1\}) = \int_{x \in A} \eta(x) \, dP_X(x)$
--   where $P_X := P.\mathrm{map}\ \mathrm{Prod.fst}$. Because the book's risks are extended-real
--   valued while `risk`/`bayesRisk` here are ordinary (junk-at-non-integrable) Bochner integrals,
--   finiteness of the relevant risk is added as an explicit integrability hypothesis on `f` in
--   each assertion — automatic in the book's own argument (bounded losses on a probability
--   space), stated here so the real-valued difference is never a vacuous `0 - 0`.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 37, Theorem 2.31 (Zhang's inequality)

import Mathlib
import Definitions.Def_SupportVectorMachines_LossFunctions_RiskBasics
import Definitions.Def_SupportVectorMachines_LossFunctions_ClassificationLosses

open MeasureTheory

namespace SupportVectorMachines.LossFunctions

/-- Theorem 2.31 (Zhang's inequality), p. 37: given a distribution `P` on `X × Y` (`Y := {-1,1}`)
with `η(x) := P(y=1|x)` and Bayes classifier `f*_{L_class,P}(x) := sign(2η(x)-1)`:

* for every measurable `f : X → [-1,1]` with finite hinge risk,
  `R_{L_hinge,P}(f) - R*_{L_hinge,P} = ∫_X |f(x) - f*_{L_class,P}(x)| · |2η(x) - 1| dP_X(x)`
  (an exact equality);
* for every measurable `f : X → ℝ` with finite hinge and classification risk,
  `R_{L_class,P}(f) - R*_{L_class,P} ≤ R_{L_hinge,P}(f) - R*_{L_hinge,P}`.

`η` is represented via its defining disintegration property: for every measurable `A ⊆ X`,
`P(A × {1}) = ∫_{x ∈ A} η(x) dP_X(x)`, where `P_X := P.map Prod.fst` is the `X`-marginal. The
finite-risk hypotheses guard the real-valued (junk-at-non-integrable) Bochner integral used for
`risk`/`bayesRisk`: the book's risks are extended-real-valued and the difference is understood
whenever the risks involved are finite, which is automatic for `L_class` (bounded by 1) and for
`L_hinge` on `f` valued in `[-1,1]` (bounded by 2), and is stated explicitly for the general `f`
of the second assertion. -/
theorem zhang_inequality {X : Type*} [MeasurableSpace X] (P : Measure (X × ℝ))
    [IsProbabilityMeasure P] (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1) (η : X → ℝ)
    (hη : ∀ A, MeasurableSet A →
      (P (A ×ˢ ({1} : Set ℝ))).toReal = ∫ x in A, η x ∂(P.map Prod.fst)) :
    (∀ f : X → ℝ, Measurable f → (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) →
        Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (f p.1)) P →
        risk hingeLoss P f - bayesRisk hingeLoss P =
          ∫ x, |f x - bayesClassifier η x| * |2 * η x - 1| ∂(P.map Prod.fst)) ∧
      ∀ f : X → ℝ, Measurable f →
        Integrable (fun p : X × ℝ => hingeLoss p.1 p.2 (f p.1)) P →
        Integrable (fun p : X × ℝ => classLoss p.1 p.2 (f p.1)) P →
        risk classLoss P f - bayesRisk classLoss P ≤
          risk hingeLoss P f - bayesRisk hingeLoss P := by sorry

end SupportVectorMachines.LossFunctions
