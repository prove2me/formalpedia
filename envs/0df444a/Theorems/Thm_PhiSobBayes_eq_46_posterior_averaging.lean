-- Prove2me | Theorems.Thm_PhiSobBayes_eq_46_posterior_averaging
-- name    : PhiSobBayes.eq_46_posterior_averaging
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:11.463078+00:00
-- url     : https://prove2.me/theorems/e5972975-6b87-4ba5-97fb-e55ff31365c7
-- title:
--   Section 6, (46) — the planted model disintegrates through the posterior, and $\mathbb E_{y\sim Y_t}\mu_{t,y}=\mu$
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^n$ and $t>0$. The planted model can be sampled in either order: draw $X\sim\mu$ and then $Y_t\sim K_{t,X}$, or draw $Y_t\sim\mu K_t$ and then $X\sim\mu_{t,Y_t}$. That is, for all measurable $A,B\subseteq\mathbb R^n$,
--   $$P_t(A\times B)=\int_B \mu_{t,y}(A)\,(\mu K_t)(dy),$$
--   and, taking $B=\mathbb R^n$, averaging the posterior over the observation recovers the prior:
--   $$\int \mu_{t,y}(A)\,(\mu K_t)(dy)=\mu(A).\tag{46}$$
--
--   This is the Nishimori identity used to average posterior statements over the observation, in Lemma 6.2 and in (49).
--
--   Differences from the source:
--   - encoding: P_t(dx, dy) = (μK_t)(dy) μ_{t,y}(dx), as an identity of measures → the identity on all measurable rectangles A × B; reason: rectangles generate the product σ-algebra, so the two forms are equivalent
--   - encoding: μ_{t,y} = L(X | Y_t = y), computed by Bayes' formula (44) → the explicit formula (44) for every y; reason: the paper's own formula; Mathlib's conditional law is only defined almost everywhere
--   - encoding: ℝⁿ → EuclideanSpace ℝ (Fin n); reason: Lean's Euclidean space; same norm, Lebesgue measure and gradient
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 6, p.29 (PDF 29), display (46)

import Mathlib
import Definitions.Def_PhiSobBayes_gamJoint
import Definitions.Def_PhiSobBayes_gamObs
import Definitions.Def_PhiSobBayes_posterior

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- **Section 6, the joint identity and (46).** For a probability measure `μ` on `ℝⁿ` and `t > 0`,
the planted model disintegrates over the observation law with the posterior as conditional law,
`P_t(dx, dy) = (μK_t)(dy) μ_{t,y}(dx)`, and averaging the posterior over the observation recovers
the prior, `𝔼_{y∼Y_t} μ_{t,y} = μ`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 6, "Planted vs null detection", p.29 (PDF 29), display (46).

**Formalization Note** The disintegration is stated on measurable rectangles `A × B`, which
determine the joint law; the second clause is the case `B = ℝⁿ`. Lower Lebesgue integrals, so no
measurability of `y ↦ μ_{t,y}(A)` is presupposed. -/
theorem eq_46_posterior_averaging {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0 < t) :
    (∀ A B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A → MeasurableSet B →
      gamJoint μ t (A ×ˢ B) = ∫⁻ y in B, posterior μ t y A ∂(gamObs μ t)) ∧
    (∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      ∫⁻ y, posterior μ t y A ∂(gamObs μ t) = μ A) := by sorry

end PhiSobBayes
