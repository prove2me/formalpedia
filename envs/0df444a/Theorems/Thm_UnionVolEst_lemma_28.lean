-- Prove2me | Theorems.Thm_UnionVolEst_lemma_28
-- name    : UnionVolEst.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:02:47.848492+00:00
-- url     : https://prove2.me/theorems/2f2407e4-3a57-48f9-bd0f-68a39373ae27
-- title:
--   Lemma 28 — Chernoff bound $\Pr(|X-\lambda|>\varepsilon\lambda)\le2e^{-\varepsilon^2\lambda/(2(1+\varepsilon))}$ for $X\sim\mathrm{Pois}(\lambda)$
-- statement:
--   Let $X\sim\mathrm{Pois}(\lambda)$ with $\lambda\ge0$. Then for every $\varepsilon>0$,
--   $$
--   \Pr\big(|X-\lambda|>\varepsilon\lambda\big)\le 2\exp\Big(-\frac{\varepsilon^2\lambda}{2(1+\varepsilon)}\Big).
--   $$
--   The bound drives the concentration steps of Claims 14, 17 and 20.
--
--   Differences from the source:
--   - generalization: X ∼ Pois(λ) (λ > 0 implicit) → λ ∈ ℝ≥0, including λ = 0; reason: at λ = 0 both sides are trivial; every λ > 0 is covered
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), Lemma 28, p.41 (PDF p.43)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace UnionVolEst

/-- Lemma 28 (Chernoff Bound for Poisson Random Variables) (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24)), printed p.41, PDF p.43: if
`X ∼ Pois(λ)`, then for every `ε > 0`, `P(|X − λ| > ελ) ≤ 2 exp(−ε²λ/(2(1 + ε)))`.

**Formalization Note** `λ ≥ 0` (`ℝ≥0`); for `λ = 0` the bound is trivial. The probability is
compared in `ℝ≥0∞` via `ENNReal.ofReal`. -/
theorem lemma_28 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (X : Ω → ℕ) (hX : HasLaw X (poissonMeasure lam) P) (ε : ℝ) (hε : 0 < ε) :
    P {ω | ε * (lam : ℝ) < |(X ω : ℝ) - lam|} ≤
      ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 * lam) / (2 * (1 + ε)))) := by sorry

end UnionVolEst
