-- Prove2me | Theorems.Thm_RiskStopTC_one_step_decomposition
-- name    : RiskStopTC.one_step_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:22.831809+00:00
-- url     : https://prove2.me/theorems/51948071-e417-49b4-9708-bb260ec45201
-- title:
--   Theorem 5.6, proof, p.21 — $\rho_{m,T}(Z_\tau)=\mathbb 1_{\{\tau=m\}}Z_m+\mathbb 1_{\{\tau>m\}}\varrho_m\big(\rho_{m+1,T}(Z_{\tau\vee(m+1)})\big)$
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space with a filtration $\mathcal F_0\subset\cdots\subset\mathcal F_T$, $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathcal F_T=\mathcal F$, and $\mathcal Z_t=L^p(\Omega,\mathcal F_t,P)$ for a fixed $p\in[1,\infty]$. Relations between random variables hold $P$-almost surely.
--
--   Let $\varrho_t$, $t<T$, be monotone, translation equivariant mappings $\mathcal Z_{t+1}\to\mathcal Z_t$ with (5.17), let $Z_t\in\mathcal Z_t$, let $m<T$ and $\tau\in\mathfrak T_m$. Then almost surely
--   $$\rho_{m,T}(Z_\tau)=\mathbb 1_{\{\tau=m\}}Z_m+\mathbb 1_{\{\tau>m\}}\,\varrho_{m|\mathcal F_m}\Big(\rho_{m+1,T}\big(Z_{\tau\vee(m+1)}\big)\Big).$$
--
--   This is the step of the backward induction that the paper writes out for $m=T-1$ and $m=T-2$: translation equivariance pulls $\mathbb 1_{\{\tau=m\}}Z_m$ out of $\varrho_m$, and (5.17) confines the rest to $\{\tau>m\}$.
--
--   Differences from the source:
--   - generalization: the displays for m = T − 1 and m = T − 2, with the inner bracket 1{τ=T−1} Z_{T−1} + 1{τ=T} ϱ_{T−1}(Z_T) → every m < T, with the inner bracket written as ρ_{m+1,T}(Z_{τ∨(m+1)}); reason: for m = T − 2 the inner bracket equals ρ_{T−1,T}(Z_{τ∨(T−1)}) by the m = T − 1 display on the same page; the general m is the induction step the paper leaves to 'going backwards in time'
--   - encoding: Z_t = L^p(Ω, F_t, P) as classes of a.e.-equal functions; ⪯ and = almost surely → functions Ω → ℝ with an F_t-measurable representative in L^p (IsLp (ℱ t) P p); relations ≤ᵐ[P] and =ᵐ[P]; reason: every class has such a representative; Lean convention; same instances
--   - encoding: stopping times τ : Ω → {0, …, T} with {τ = t} ∈ F_t; 𝔗_m = {τ ∈ 𝔗 : τ ≥ m} → IsBddStoppingTime ℱ T τ (Mathlib IsStoppingTime, values in WithTop ℕ, τ ≤ T everywhere) and m ≤ τ everywhere (IsStopTimeFrom); reason: in discrete time {τ ≤ t} ∈ F_t for all t is equivalent to {τ = t} ∈ F_t for all t; same instances
--   - encoding: monotone translation equivariant mappings ϱ_t|F_t : Z_{t+1} → Z_t with (5.17), t = 0, …, T − 1 → one family ϱ : ℕ → (Ω → ℝ) → Ω → ℝ with IsStoppingFamily (maps-to, monotone, translation equivariant, (5.17)) on IsLp (ℱ (t+1)) arguments, t < T; reason: values off Z_{t+1} and maps with t ≥ T are never used; monotonicity makes each ϱ_t respect a.e. equality, so it acts on classes; same instances
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, Theorem 5.6, proof, p.21 (displays for m = T−1 and m = T−2, "where the last equation holds since … and by (5.17)")

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_RiskStopTC_IsStoppingFamily
import Definitions.Def_RiskStopTC_nested
import Definitions.Def_RiskStopTC_stoppedRV
import Definitions.Def_RiskStopTC_IsStopTimeFrom

open MeasureTheory RiskFunctionals.NestedAVaR

namespace RiskStopTC

/-- **One-step decomposition of the stopped value.** Pichler, Liu & Shapiro, arXiv:1808.10807v3,
Theorem 5.6, proof, p.21: "ρT−2,T(Zτ) = … = 1{τ=T−2} ZT−2 + 1{τ>T−2} ϱT−2|FT−2(1{τ=T−1} ZT−1 +
1{τ=T} ϱT−1|FT−1(ZT)), where the last equation holds since 1{τ>T−2} 1{τ=T−1} = 1{τ=T−1} and
1{τ>T−2} 1{τ=T} = 1{τ=T} and by (5.17)."

For `m < T` and `τ ∈ 𝔗_m`:
`ρ_{m,T}(Z_τ) = 1{τ=m} Z_m + 1{τ>m} ϱ_m(ρ_{m+1,T}(Z_{τ∨(m+1)}))` a.s.

**Formalization Note.** `τ ∨ (m+1)` is `fun ω => max (τ ω) (m+1)` in `WithTop ℕ`; it lies in
`𝔗_{m+1}` and equals `τ` on `{τ > m}`. The paper prints `m = T − 2` and `m = T − 1`; the
statement is for every `m < T`. -/
theorem one_step_decomposition {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (hϱ : IsStoppingFamily ℱ P p T ϱ)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ t ≤ T, IsLp (ℱ t) P p (Z t))
    (m : ℕ) (hm : m < T) (τ : Ω → WithTop ℕ) (hτ : IsStopTimeFrom ℱ T m τ) :
    nested ϱ m T (stoppedRV Z τ T) =ᵐ[P]
      ({ω | τ ω = (m : WithTop ℕ)}).indicator (Z m) +
        ({ω | (m : WithTop ℕ) < τ ω}).indicator
          (ϱ m (nested ϱ (m + 1) T
            (stoppedRV Z (fun ω => max (τ ω) ((m + 1 : ℕ) : WithTop ℕ)) T))) := by sorry

end RiskStopTC
