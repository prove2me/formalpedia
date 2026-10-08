-- Prove2me | Theorems.Thm_SolomonRWRE_Recurrence_proof_1_7_log_moment
-- name    : SolomonRWRE.Recurrence.proof_1_7_log_moment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:12.983699+00:00
-- url     : https://prove2.me/theorems/a8f88add-8b3e-45d8-9845-8778b8600ab0
-- title:
--   §1, proof of Theorem (1.7), p. 5 — E(ln σ) < 0 iff S_n → −∞ a.e. iff Σ (1/n)P(ρ_n > 1) = Σ (1/n)P(S_n > 0) < ∞
-- statement:
--   Let $(X_n)$ be the random walk in the i.i.d. random environment $\alpha=(\alpha_n)_{n\in\mathbb Z}$, where $\alpha_0$ is nondegenerate and either $0\le\alpha_n<1$ for all $n$ or $0<\alpha_n\le1$ for all $n$. Let $\sigma_n=(1-\alpha_n)/\alpha_n\in[0,\infty]$, $\rho_n=\sigma_1\cdots\sigma_n$, and
--   $$S_n=\ln\sigma_1+\dots+\ln\sigma_n\in[-\infty,\infty].$$
--   Suppose that $E(\ln\sigma)$ is defined (possibly $\pm\infty$). Then
--   $$E(\ln\sigma)<0\iff\lim_{n\to\infty}S_n=-\infty\ \text{a.s.}\iff\sum_{n=1}^\infty\frac1nP(\rho_n>1)<\infty,$$
--   and
--   $$\sum_{n=1}^\infty\frac1nP(\rho_n>1)=\sum_{n=1}^\infty\frac1nP(S_n>0).$$
--
--   This identifies the series condition (i) of Theorem (1.7) with the sign condition (i′) $E(\ln\sigma)<0$.
--
--   **Formalization Note** $\ln 0=-\infty$ and $\ln\infty=+\infty$; the range hypothesis keeps $-\infty+\infty$ out of $S_n$. "$S_n\to-\infty$" is convergence to $-\infty$ in the extended reals. $E(\ln\sigma)=E(\ln\sigma)^+-E(\ln\sigma)^-$, and "defined" means one of the two parts is finite.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 5, §1, proof of Theorem (1.7), second paragraph

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SolomonRWRE.Recurrence

/-- Solomon, *Random Walks in a Random Environment*, Ann. Probab. 3(1) (1975), §1, proof of
Theorem (1.7), p. 5, second paragraph: suppose `E(ln σ)` is defined and set
`S_n = ln σ_1 + ⋯ + ln σ_n`. Then `E(ln σ) < 0` if and only if `S_n → −∞` a.e. if and only if
`Σ_{n=1}^∞ (1/n) P(ρ_n > 1) = Σ_{n=1}^∞ (1/n) P(S_n > 0) < ∞`.

**Formalization Note.** The hypotheses are those of Theorem (1.7): the random walk in a random
environment with `α_0` nondegenerate and `0 ≤ α_n < 1` for all `n` or `0 < α_n ≤ 1` for all
`n`. `ln σ_n` and `S_n` (`logSum`) are extended reals (`ln 0 = −∞`, `ln ∞ = +∞`); the range
hypothesis rules out `−∞ + ∞` in `S_n`. "`S_n → −∞`" is convergence to `⊥` in `[−∞, ∞]`.
`E(ln σ)` is `E[(ln σ)⁺] − E[(ln σ)⁻]` with both parts in `[0, ∞]` (`logMoment`); "defined"
means one of them is finite. The series are in `[0, ∞]`, over `n ≥ 1` (Lean index `n + 1`). -/
theorem proof_1_7_log_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (hRW : IsRWRE P α X)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c)
    (hrange : (∀ n ω, 0 ≤ α n ω ∧ α n ω < 1) ∨ (∀ n ω, 0 < α n ω ∧ α n ω ≤ 1))
    (hdef : LogMomentDefined P α) :
    (logMoment P α < 0 ↔ ∀ᵐ ω ∂P, Tendsto (fun n => logSum α n ω) atTop (𝓝 ⊥)) ∧
    ((∀ᵐ ω ∂P, Tendsto (fun n => logSum α n ω) atTop (𝓝 ⊥)) ↔ seriesGt P α ≠ ∞) ∧
    seriesGt P α = ∑' n : ℕ, ((n : ℝ≥0∞) + 1)⁻¹ * P {ω | 0 < logSum α (n + 1) ω} := by sorry

end SolomonRWRE.Recurrence
