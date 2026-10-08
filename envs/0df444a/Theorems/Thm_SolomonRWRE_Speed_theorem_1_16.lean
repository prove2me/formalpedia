-- Prove2me | Theorems.Thm_SolomonRWRE_Speed_theorem_1_16
-- name    : SolomonRWRE.Speed.theorem_1_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:28.842986+00:00
-- url     : https://prove2.me/theorems/f29c0db8-fdde-409f-8a83-e9d1c221d253
-- title:
--   Theorem (1.16) — three-case speed and passage-time law
-- statement:
--   For the annealed nearest-neighbor walk, set $e=E\sigma$ and $e_-=E(\sigma^{-1})$, where $\sigma=(1-\alpha_0)/\alpha_0$. Both means may be infinite. The following limits hold almost surely.
--
--   1. If $e<1$, then
--      $$\frac{T_n}{n}\longrightarrow\frac{1+e}{1-e},\qquad
--      \frac{X_n}{n}\longrightarrow\frac{1-e}{1+e}.$$
--   2. If $e_-<1$, then
--      $$\frac{T_{-n}}{n}\longrightarrow\frac{1+e_-}{1-e_-},\qquad
--      \frac{X_n}{n}\longrightarrow-\frac{1-e_-}{1+e_-}.$$
--   3. If $e^{-1}\le1\le e_-$, then
--      $$\frac{T_n}{n}\longrightarrow\infty,\qquad
--      \frac{T_{-n}}{n}\longrightarrow\infty,\qquad
--      \frac{X_n}{n}\longrightarrow0.$$
--
--   This is Solomon's law for asymptotic speed, including the corresponding passage-time limits in all three regimes.
--
--   **Formalization Note** The reciprocal condition in case 3 is stated in extended nonnegative arithmetic and covers $e=\infty$. Passage times can themselves be infinite; $X_n/n$ has a real limit. The walk law is the joint annealed law, with independent, identically distributed site probabilities in $[0,1]$.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 7, Theorem (1.16)

import Mathlib
import Definitions.Def_SolomonRWRE_Speed_Model

namespace SolomonRWRE.Speed

/-- Solomon (1975), p. 7, Theorem (1.16). All three cases, including both
passage-time limits in each case. **Formalization Note:** passage times take
values in `ℕ∞` and their normalized limits in `ℝ≥0∞`; `σ` and its expectations
are extended nonnegative, preserving environments with α equal to 0 or 1. -/
theorem theorem_1_16 {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (h : SolomonRWRE.Recurrence.IsRWRE P α X) :
    (meanSigma P α < 1 →
      (∀ᵐ ω ∂P, Filter.Tendsto
        (fun n : ℕ => ENat.toENNReal (passageTime X (n : ℤ) ω) / (n : ENNReal))
        Filter.atTop (nhds (ENNReal.ofReal
          ((1 + (meanSigma P α).toReal) / (1 - (meanSigma P α).toReal))))) ∧
      (∀ᵐ ω ∂P, Filter.Tendsto
        (fun n : ℕ => (X n ω : ℝ) / (n : ℝ)) Filter.atTop
        (nhds ((1 - (meanSigma P α).toReal) / (1 + (meanSigma P α).toReal))))) ∧
    (meanInvSigma P α < 1 →
      (∀ᵐ ω ∂P, Filter.Tendsto
        (fun n : ℕ => ENat.toENNReal (passageTime X (-(n : ℤ)) ω) / (n : ENNReal))
        Filter.atTop (nhds (ENNReal.ofReal
          ((1 + (meanInvSigma P α).toReal) / (1 - (meanInvSigma P α).toReal))))) ∧
      (∀ᵐ ω ∂P, Filter.Tendsto
        (fun n : ℕ => (X n ω : ℝ) / (n : ℝ)) Filter.atTop
        (nhds (-((1 - (meanInvSigma P α).toReal) / (1 + (meanInvSigma P α).toReal)))))) ∧
    ((meanSigma P α)⁻¹ ≤ 1 ∧ 1 ≤ meanInvSigma P α →
      (∀ᵐ ω ∂P, Filter.Tendsto
        (fun n : ℕ => ENat.toENNReal (passageTime X (n : ℤ) ω) / (n : ENNReal))
        Filter.atTop (nhds (⊤ : ENNReal))) ∧
      (∀ᵐ ω ∂P, Filter.Tendsto
        (fun n : ℕ => ENat.toENNReal (passageTime X (-(n : ℤ)) ω) / (n : ENNReal))
        Filter.atTop (nhds (⊤ : ENNReal))) ∧
      (∀ᵐ ω ∂P, Filter.Tendsto
        (fun n : ℕ => (X n ω : ℝ) / (n : ℝ)) Filter.atTop (nhds 0))) := by sorry

end SolomonRWRE.Speed
