-- Prove2me | Theorems.Thm_RiskStopTC_eq_5_2
-- name    : RiskStopTC.eq_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:33.093769+00:00
-- url     : https://prove2.me/theorems/89860a5c-9dc2-4b60-bdcb-490037263705
-- title:
--   (5.2), p.17 — the stopping risk measure $\rho_{m,T}(Z_\tau)=\mathbb 1_{\{\tau=m\}}Z_m+\varrho_m(\cdots\varrho_{T-1}(\mathbb 1_{\{\tau=T\}}Z_T))$
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space with a filtration $\mathcal F_0\subset\cdots\subset\mathcal F_T$, $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathcal F_T=\mathcal F$, and $\mathcal Z_t=L^p(\Omega,\mathcal F_t,P)$ for a fixed $p\in[1,\infty]$. Relations between random variables hold $P$-almost surely.
--
--   Let $\varrho_t$, $t<T$, be monotone, translation equivariant mappings $\mathcal Z_{t+1}\to\mathcal Z_t$ with (5.17), let $Z_t\in\mathcal Z_t$, let $m\le T$ and $\tau\in\mathfrak T_m$. Define $W_T=\mathbb 1_{\{\tau=T\}}Z_T$ and $W_t=\mathbb 1_{\{\tau=t\}}Z_t+\varrho_{t|\mathcal F_t}(W_{t+1})$ for $t<T$. Then
--   $$\rho_{m,T}(Z_\tau)=W_m\quad\text{a.s.}$$
--   For $m=0$ this is the stopping risk measure (5.2):
--   $$\rho_{0,T}(Z_\tau)=\mathbb 1_{\{\tau=0\}}Z_0+\varrho_{0|\mathcal F_0}\Big(\mathbb 1_{\{\tau=1\}}Z_1+\cdots+\varrho_{T-1|\mathcal F_{T-1}}\big(\mathbb 1_{\{\tau=T\}}Z_T\big)\Big).$$
--
--   Differences from the source:
--   - generalization: (5.2) at m = 0: ρ_{0,T}(Z_τ) = 1{τ=0} Z_0 + ϱ_0(1{τ=1} Z_1 + ⋯ + ϱ_{T−1}(1{τ=T} Z_T)) for τ ∈ 𝔗 → ρ_{m,T}(Z_τ) = W_m a.s. for every m ≤ T and τ ∈ 𝔗_m, with the bracket written as the recursion W (stopRiskRec); reason: m = 0 (𝔗_0 = 𝔗) gives (5.2); the general start is the conditional version used in the proof of Theorem 5.6
--   - encoding: Z_t = L^p(Ω, F_t, P) as classes of a.e.-equal functions; ⪯ and = almost surely → functions Ω → ℝ with an F_t-measurable representative in L^p (IsLp (ℱ t) P p); relations ≤ᵐ[P] and =ᵐ[P]; reason: every class has such a representative; Lean convention; same instances
--   - encoding: stopping times τ : Ω → {0, …, T} with {τ = t} ∈ F_t; 𝔗_m = {τ ∈ 𝔗 : τ ≥ m} → IsBddStoppingTime ℱ T τ (Mathlib IsStoppingTime, values in WithTop ℕ, τ ≤ T everywhere) and m ≤ τ everywhere (IsStopTimeFrom); reason: in discrete time {τ ≤ t} ∈ F_t for all t is equivalent to {τ = t} ∈ F_t for all t; same instances
--   - encoding: monotone translation equivariant mappings ϱ_t|F_t : Z_{t+1} → Z_t with (5.17), t = 0, …, T − 1 → one family ϱ : ℕ → (Ω → ℝ) → Ω → ℝ with IsStoppingFamily (maps-to, monotone, translation equivariant, (5.17)) on IsLp (ℱ (t+1)) arguments, t < T; reason: values off Z_{t+1} and maps with t ≥ T are never used; monotonicity makes each ϱ_t respect a.e. equality, so it acts on classes; same instances
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, equation (5.2), p.17

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_RiskStopTC_IsStoppingFamily
import Definitions.Def_RiskStopTC_nested
import Definitions.Def_RiskStopTC_stoppedRV
import Definitions.Def_RiskStopTC_stopRiskRec
import Definitions.Def_RiskStopTC_IsStopTimeFrom

open MeasureTheory RiskFunctionals.NestedAVaR

namespace RiskStopTC

/-- **The stopping risk measure (5.2).** Pichler, Liu & Shapiro, arXiv:1808.10807v3, (5.2), p.17:
"The stopping risk measure is ρ0,T(Zτ) = 1{τ=0} Z0 + ϱ0|F0(1{τ=1} Z1 + · · · +
ϱT−1|FT−1(1{τ=T} ZT)). (5.2) The stopping risk measure is well-defined by virtue of (2.4) and the
translation equivariance of the mappings ϱt|Ft."

For `m ≤ T` and `τ ∈ 𝔗_m`: `ρ_{m,T}(Z_τ) = W_m` a.s., where `W_T = 1{τ=T} Z_T` and
`W_t = 1{τ=t} Z_t + ϱ_t(W_{t+1})`. For `m = 0` this is (5.2).

**Formalization Note.** `W` is `stopRiskRec ϱ Z τ T`. The paper prints `m = 0`; the statement is
for every starting date `m` (for `m = 0`, `𝔗_0 = 𝔗`). -/
theorem eq_5_2 {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (hϱ : IsStoppingFamily ℱ P p T ϱ)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ t ≤ T, IsLp (ℱ t) P p (Z t))
    (m : ℕ) (hm : m ≤ T) (τ : Ω → WithTop ℕ) (hτ : IsStopTimeFrom ℱ T m τ) :
    nested ϱ m T (stoppedRV Z τ T) =ᵐ[P] stopRiskRec ϱ Z τ T m := by sorry

end RiskStopTC
