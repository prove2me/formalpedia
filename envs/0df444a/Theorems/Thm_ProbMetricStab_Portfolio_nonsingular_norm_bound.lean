-- Prove2me | Theorems.Thm_ProbMetricStab_Portfolio_nonsingular_norm_bound
-- name    : ProbMetricStab.Portfolio.nonsingular_norm_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:01.589991+00:00
-- url     : https://prove2.me/theorems/da784e73-c99b-489f-87c3-a41395d43199
-- title:
--   Proof of Theorem 5.2, p. 25 — Γ nonsingular ⇒ ∃ c > 0, c‖x‖² ≤ ∫|⟨x, ξ⟩|²Γ(dξ) for all x ∈ ℝ^s
-- statement:
--   Let $\Gamma$ be a Borel probability measure on the unit sphere $\Sigma^s\subset\mathbb R^s$ that is nonsingular, i.e. $\int_{\Sigma^s}|\langle x,\xi\rangle|^2\Gamma(d\xi)=0$ implies $x=0$. Then there is a constant $c=c(s,\Gamma)>0$ such that
--   $$c\,\|x\|^2\le\int_{\Sigma^s}|\langle x,\xi\rangle|^2\,\Gamma(d\xi)\qquad\text{for all }x\in\mathbb R^s.$$
--
--   Nonsingularity thus makes the quadratic form in the growth condition of Lemma 5.1 equivalent to the squared Euclidean norm.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 25, proof of Theorem 5.2 (sentence after "The additional assumption implies")

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting

open MeasureTheory
open scoped ENNReal

namespace ProbMetricStab.Portfolio
theorem nonsingular_norm_bound {s : ℕ} (Γ : Measure (Rs s)) (hΓ : IsSpectral Γ)
    (hns : Nonsingular Γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Rs s,
      c * ‖x‖ ^ 2 ≤ ∫ ξ in unitSphere s, |(inner ℝ x ξ : ℝ)| ^ 2 ∂Γ := by sorry
end ProbMetricStab.Portfolio
