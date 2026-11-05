-- Prove2me | Theorems.Thm_RiskStopTC_eq_2_4
-- name    : RiskStopTC.eq_2_4
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:34:55.909451+00:00
-- url     : https://prove2.me/theorems/df61fd05-06a9-4fb0-a996-d9027a97ce44
-- title:
--   (2.4), p.5 — the stopped reward $Z_\tau=\sum_{t=0}^T\mathbb 1_{\{\tau=t\}}Z_t$ and $Z_\tau\in\mathcal Z_T$
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space with a filtration $\mathcal F_0\subset\cdots\subset\mathcal F_T$, $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathcal F_T=\mathcal F$, and $\mathcal Z_t=L^p(\Omega,\mathcal F_t,P)$ for a fixed $p\in[1,\infty]$. Relations between random variables hold $P$-almost surely.
--
--   Let $Z_t\in\mathcal Z_t$ for $t=0,\dots,T$ and let $\tau$ be a stopping time with values in $\{0,\dots,T\}$. Then for every $\omega$ and $t\le T$ with $\tau(\omega)=t$,
--   $$\sum_{s=0}^T\mathbb 1_{\{\tau=s\}}(\omega)Z_s(\omega)=Z_t(\omega),$$
--   and the stopped reward $Z_\tau=\sum_{t=0}^T\mathbb 1_{\{\tau=t\}}Z_t$ belongs to $\mathcal Z_T$.
--
--   This is the representation (2.4) through which the risk functionals act on stopped rewards.
--
--   Differences from the source:
--   - encoding: Z_τ (the value Z_{τ(ω)}(ω)) = Σ_t 1{τ=t} Z_t → Z_τ is defined as the sum (stoppedRV); the identity is stated pointwise: the sum equals Z_t(ω) when τ(ω) = t ≤ T; reason: Z_{τ(ω)}(ω) is not a Lean term of the right shape; the pointwise statement is the same identity
--   - generalization: (2.4) for (Z_0, …, Z_T) ∈ Z_{0,T} → also concludes Z_τ ∈ Z_T (IsLp (ℱ T) P p); reason: the paper presupposes Z_τ ∈ Z_T when it applies ρ_{0,T} to Z_τ (p.17); dropping the second conjunct gives (2.4)
--   - encoding: Z_t = L^p(Ω, F_t, P) as classes of a.e.-equal functions; ⪯ and = almost surely → functions Ω → ℝ with an F_t-measurable representative in L^p (IsLp (ℱ t) P p); relations ≤ᵐ[P] and =ᵐ[P]; reason: every class has such a representative; Lean convention; same instances
--   - encoding: stopping times τ : Ω → {0, …, T} with {τ = t} ∈ F_t; 𝔗_m = {τ ∈ 𝔗 : τ ≥ m} → IsBddStoppingTime ℱ T τ (Mathlib IsStoppingTime, values in WithTop ℕ, τ ≤ T everywhere) and m ≤ τ everywhere (IsStopTimeFrom); reason: in discrete time {τ ≤ t} ∈ F_t for all t is equivalent to {τ = t} ∈ F_t for all t; same instances
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, equation (2.4), p.5

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_RiskStopTC_stoppedRV

open MeasureTheory RiskFunctionals.NestedAVaR

namespace RiskStopTC

/-- **The stopped reward (2.4).** Pichler, Liu & Shapiro, arXiv:1808.10807v3, (2.4), p.5: "Moreover
1{τ=t} Zτ = 1{τ=t} Zt and thus for (Z0, . . . , ZT) ∈ Z0,T it follows that
Zτ = ∑_{t=0}^T 1{τ=t} Zτ = ∑_{t=0}^T 1{τ=t} Zt."

For `(Z_0, …, Z_T) ∈ Z_{0,T}` and a stopping time `τ` with values in `{0, …, T}`:
`∑_{t=0}^T 1{τ=t}(ω) Z_t(ω) = Z_t(ω)` whenever `τ(ω) = t ≤ T`, and `Z_τ ∈ Z_T`.

**Formalization Note.** `Z_t ∈ Z_t = L^p(Ω, F_t, P)` is `IsLp (ℱ t) P p (Z t)`; stopping times are
`IsBddStoppingTime ℱ T τ` (values in `WithTop ℕ`, `τ ≤ T` everywhere). -/
theorem eq_2_4 {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ t ≤ T, IsLp (ℱ t) P p (Z t))
    (τ : Ω → WithTop ℕ) (hτ : MultiperiodRisk.Bellman.IsBddStoppingTime ℱ T τ) :
    (∀ ω, ∀ t ≤ T, τ ω = (t : WithTop ℕ) → stoppedRV Z τ T ω = Z t ω) ∧
      IsLp (ℱ T) P p (stoppedRV Z τ T) := by sorry

end RiskStopTC
