-- Prove2me | Theorems.Thm_SolomonRWRE_Recurrence_lemma_1_6
-- name    : SolomonRWRE.Recurrence.lemma_1_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:45.107094+00:00
-- url     : https://prove2.me/theorems/07f9fc42-ea5c-46df-898f-e0f234d01169
-- title:
--   Lemma (1.6) — Σ n⁻¹P(S_n > 0) < ∞ iff S_n → −∞ a.e. (then Σ e^{S_n} < ∞), and the oscillating case
-- statement:
--   Let $Y_1,Y_2,\dots$ be independent, identically distributed, nondegenerate (not almost surely constant), real-valued random variables, and $S_n=Y_1+\dots+Y_n$.
--
--   1. $\sum_{n=1}^\infty n^{-1}P(S_n>0)<\infty$ if and only if $\lim_{n\to\infty}S_n=-\infty$ almost surely, in which case
--   $$\sum_{n=1}^\infty e^{S_n}<\infty\quad\text{almost surely.}$$
--   2. $\sum_{n=1}^\infty n^{-1}P(S_n>0)=\infty=\sum_{n=1}^\infty n^{-1}P(S_n<0)$ if and only if $-\infty=\liminf_{n\to\infty}S_n<\limsup_{n\to\infty}S_n=\infty$ almost surely, in which case
--   $$\sum_{n=1}^\infty e^{-S_n}=\infty=\sum_{n=1}^\infty e^{S_n}\quad\text{almost surely.}$$
--
--   The equivalences are the fluctuation-theory criteria of Spitzer type; the series of exponentials are what is needed when $S_n=\ln\rho_n$, since then $e^{S_n}=\rho_n$.
--
--   **Formalization Note** The sequence is indexed from $0$ in Lean (`Y j` is $Y_{j+1}$). All series are in $[0,\infty]$, with $e^{\pm S_n}$ embedded in $[0,\infty]$, so "$<\infty$" and "$=\infty$" are literal.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 3, Lemma (1.6)

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SolomonRWRE.Recurrence

/-- Solomon, *Random Walks in a Random Environment*, Ann. Probab. 3(1) (1975), p. 3,
Lemma (1.6): let `Y_1, Y_2, …` be independent, identically distributed, nondegenerate, finite
valued random variables and `S_n = Y_1 + ⋯ + Y_n`.
(i) `Σ n⁻¹ P(S_n > 0) < ∞` if and only if `S_n → −∞` a.e., in which case `Σ e^{S_n} < ∞` a.e.
(ii) `Σ n⁻¹ P(S_n > 0) = ∞ = Σ n⁻¹ P(S_n < 0)` if and only if
`−∞ = lim inf S_n < lim sup S_n = ∞` a.e., in which case `Σ e^{−S_n} = ∞ = Σ e^{S_n}` a.e.

**Formalization Note.** `Y j` is the paper's `Y_{j+1}` and `partialSum Y n` is `S_n`. All series
run over `n ≥ 1` (Lean index `n + 1`) and are in `[0, ∞]`, so "`< ∞`" is `≠ ∞`. "Finite valued"
is the type `ℝ`. Nondegenerate: `Y_1` is not almost surely constant. Each "in which case" clause
is part of the claim. -/
theorem lemma_1_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (Y j)) (hind : iIndepFun Y P)
    (hid : ∀ j, IdentDistrib (Y j) (Y 0) P P) (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, Y 0 ω = c) :
    ((∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 0 < partialSum Y (n + 1) ω} ≠ ∞ ↔
        ∀ᵐ ω ∂P, Tendsto (fun n => partialSum Y n ω) atTop atBot) ∧
      ((∀ᵐ ω ∂P, Tendsto (fun n => partialSum Y n ω) atTop atBot) →
        ∀ᵐ ω ∂P, ∑' n : ℕ, ENNReal.ofReal (Real.exp (partialSum Y (n + 1) ω)) ≠ ∞)) ∧
    ((∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 0 < partialSum Y (n + 1) ω} = ∞ ∧
        ∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | partialSum Y (n + 1) ω < 0} = ∞ ↔
        ∀ᵐ ω ∂P, Oscillates (fun n => partialSum Y n ω)) ∧
      ((∀ᵐ ω ∂P, Oscillates (fun n => partialSum Y n ω)) →
        ∀ᵐ ω ∂P, ∑' n : ℕ, ENNReal.ofReal (Real.exp (-partialSum Y (n + 1) ω)) = ∞ ∧
          ∑' n : ℕ, ENNReal.ofReal (Real.exp (partialSum Y (n + 1) ω)) = ∞)) := by sorry

end SolomonRWRE.Recurrence
