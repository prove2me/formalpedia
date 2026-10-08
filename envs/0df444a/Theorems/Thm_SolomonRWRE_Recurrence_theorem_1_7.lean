-- Prove2me | Theorems.Thm_SolomonRWRE_Recurrence_theorem_1_7
-- name    : SolomonRWRE.Recurrence.theorem_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:43.066499+00:00
-- url     : https://prove2.me/theorems/09a9f1e5-e70a-4ce6-a7f4-e6164f8c04f7
-- title:
--   Theorem (1.7) — X_n → ∞, X_n → −∞, or −∞ = lim inf X_n < lim sup X_n = ∞ a.e., according to Σ n⁻¹P(ρ_n > 1), Σ n⁻¹P(ρ_n < 1); and E(ln σ) < 0, > 0, = 0
-- statement:
--   Let $\{\alpha_n\}_{-\infty}^{\infty}$ be a sequence of independent, identically distributed, nondegenerate random variables with $0\le\alpha_n<1$ for all $n$ or $0<\alpha_n\le1$ for all $n$, and let $(X_n)$ be the random walk in the random environment $\{\alpha_n\}$, started at $0$. Let $\sigma_n=(1-\alpha_n)/\alpha_n\in[0,\infty]$ and $\rho_n=\sigma_1\cdots\sigma_n$.
--
--   1. If $\sum_{n=1}^\infty n^{-1}P(\rho_n>1)<\infty$, then $\lim_{n\to\infty}X_n=\infty$ almost surely.
--   2. If $\sum_{n=1}^\infty n^{-1}P(\rho_n<1)<\infty$, then $\lim_{n\to\infty}X_n=-\infty$ almost surely.
--   3. If $\sum_{n=1}^\infty n^{-1}P(\rho_n<1)=\infty=\sum_{n=1}^\infty n^{-1}P(\rho_n>1)$, then $\{X_n\}$ is recurrent; in fact
--   $$-\infty=\liminf_{n\to\infty}X_n<\limsup_{n\to\infty}X_n=\infty\quad\text{almost surely.}$$
--
--   If $E(\ln\sigma)$ is defined (possibly $\pm\infty$), then the hypotheses of (i), (ii), (iii) correspond respectively to
--   $$\text{(i}'\text{)}\ E(\ln\sigma)<0,\qquad\text{(ii}'\text{)}\ E(\ln\sigma)>0,\qquad\text{(iii}'\text{)}\ E(\ln\sigma)=0 .$$
--
--   The theorem gives a complete classification of the limit behaviour of the random walk in an i.i.d. random environment on $\mathbb Z$ in terms of the law of $\alpha_0$ alone: the walk is transient to the right, transient to the left, or recurrent.
--
--   **Formalization Note** The series are in $[0,\infty]$. "Correspond respectively" is formalized as three equivalences: $\sum n^{-1}P(\rho_n>1)<\infty\iff E(\ln\sigma)<0$, $\sum n^{-1}P(\rho_n<1)<\infty\iff E(\ln\sigma)>0$, and (both series infinite) $\iff E(\ln\sigma)=0$. $E(\ln\sigma)=E(\ln\sigma)^+-E(\ln\sigma)^-$ in $[-\infty,\infty]$, with "defined" meaning one of the two parts is finite. Nondegenerate means $\alpha_0$ is not almost surely constant; without it ($\alpha\equiv\tfrac12$) both series vanish and (i), (ii) would contradict each other.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 4, Theorem (1.7)

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SolomonRWRE.Recurrence

/-- Solomon, *Random Walks in a Random Environment*, Ann. Probab. 3(1) (1975), p. 4,
Theorem (1.7). Let `{α_n}_{−∞}^∞` be independent, identically distributed, nondegenerate random
variables with `0 ≤ α_n < 1` for all `n` or `0 < α_n ≤ 1` for all `n`, and let `X` be the random
walk in the random environment `α`.
(i) If `Σ_{n=1}^∞ n⁻¹ P(ρ_n > 1) < ∞`, then `X_n → ∞` a.e.
(ii) If `Σ_{n=1}^∞ n⁻¹ P(ρ_n < 1) < ∞`, then `X_n → −∞` a.e.
(iii) If both series are `∞`, then `{X_n}` is recurrent; in fact
`−∞ = lim inf X_n < lim sup X_n = ∞` a.e.
If `E(ln σ)` is defined (possibly `±∞`), then (i), (ii), (iii) correspond respectively to
(i′) `E(ln σ) < 0`, (ii′) `E(ln σ) > 0`, (iii′) `E(ln σ) = 0`.

**Formalization Note.** `seriesGt`/`seriesLt` are the two series in `[0, ∞]` (over `n ≥ 1`), so
"`< ∞`" is `≠ ∞`. `σ_n = (1 − α_n)/α_n ∈ [0, ∞]` and `ρ_n = σ_1 ⋯ σ_n`; the range hypothesis
keeps `0 · ∞` out of `ρ_n`. Nondegenerate: `α_0` is not almost surely constant. "Correspond
respectively" is read as the equivalence of each case's hypothesis with the matching sign
condition on `E(ln σ) = E[(ln σ)⁺] − E[(ln σ)⁻] ∈ [−∞, ∞]`, where "defined" means one of the two
parts is finite. -/
theorem theorem_1_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (hRW : IsRWRE P α X)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c)
    (hrange : (∀ n ω, 0 ≤ α n ω ∧ α n ω < 1) ∨ (∀ n ω, 0 < α n ω ∧ α n ω ≤ 1)) :
    (seriesGt P α ≠ ∞ → ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop) ∧
    (seriesLt P α ≠ ∞ → ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot) ∧
    (seriesLt P α = ∞ ∧ seriesGt P α = ∞ → ∀ᵐ ω ∂P, Oscillates (fun n => X n ω)) ∧
    (LogMomentDefined P α →
      (seriesGt P α ≠ ∞ ↔ logMoment P α < 0) ∧
      (seriesLt P α ≠ ∞ ↔ 0 < logMoment P α) ∧
      (seriesLt P α = ∞ ∧ seriesGt P α = ∞ ↔ logMoment P α = 0)) := by sorry

end SolomonRWRE.Recurrence
