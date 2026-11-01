-- Prove2me | Theorems.Thm_RiskStopTC_eq_5_18
-- name    : RiskStopTC.eq_5_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:29.7025+00:00
-- url     : https://prove2.me/theorems/0173b10e-a942-48da-85b2-c8fdcacf45de
-- title:
--   (5.18), p.21 — the domination step: $\rho_{m+1,T}(Z_{\tau\vee(m+1)})\preceq E_{m+1}$ implies $\rho_{m,T}(Z_\tau)\preceq E_m$
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space with a filtration $\mathcal F_0\subset\cdots\subset\mathcal F_T$, $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathcal F_T=\mathcal F$, and $\mathcal Z_t=L^p(\Omega,\mathcal F_t,P)$ for a fixed $p\in[1,\infty]$. Relations between random variables hold $P$-almost surely.
--
--   Let $\varrho_t$, $t<T$, be monotone, translation equivariant mappings $\mathcal Z_{t+1}\to\mathcal Z_t$ with (5.17), let $Z_t\in\mathcal Z_t$, and let $E$ be the Snell envelope (5.14). Let $m<T$ and $\tau\in\mathfrak T_m$. If
--   $$\rho_{m+1,T}\big(Z_{\tau\vee(m+1)}\big)\preceq E_{m+1},$$
--   then
--   $$\rho_{m,T}(Z_\tau)\preceq E_m.$$
--
--   For $m=T-1$ the hypothesis is $Z_T\preceq E_T=Z_T$ and the conclusion is (5.18) with "It follows that $\rho_{T-1,T}(Z_\tau)\preceq E_{T-1}$"; for $m=T-2$ it is the next step on the same page. Iterating it gives the first half of clause (i) of Theorem 5.6.
--
--   Differences from the source:
--   - generalization: (5.18) and its consequence for m = T − 1, and the analogous step for m = T − 2 → the induction step for every m < T, with hypothesis ρ_{m+1,T}(Z_{τ∨(m+1)}) ⪯ E_{m+1}; reason: at m = T − 1 the hypothesis is Z_T ⪯ E_T = Z_T, true, and the conclusion is the page's; at m = T − 2 the hypothesis is the m = T − 1 result
--   - encoding: Z_t = L^p(Ω, F_t, P) as classes of a.e.-equal functions; ⪯ and = almost surely → functions Ω → ℝ with an F_t-measurable representative in L^p (IsLp (ℱ t) P p); relations ≤ᵐ[P] and =ᵐ[P]; reason: every class has such a representative; Lean convention; same instances
--   - encoding: stopping times τ : Ω → {0, …, T} with {τ = t} ∈ F_t; 𝔗_m = {τ ∈ 𝔗 : τ ≥ m} → IsBddStoppingTime ℱ T τ (Mathlib IsStoppingTime, values in WithTop ℕ, τ ≤ T everywhere) and m ≤ τ everywhere (IsStopTimeFrom); reason: in discrete time {τ ≤ t} ∈ F_t for all t is equivalent to {τ = t} ∈ F_t for all t; same instances
--   - encoding: monotone translation equivariant mappings ϱ_t|F_t : Z_{t+1} → Z_t with (5.17), t = 0, …, T − 1 → one family ϱ : ℕ → (Ω → ℝ) → Ω → ℝ with IsStoppingFamily (maps-to, monotone, translation equivariant, (5.17)) on IsLp (ℱ (t+1)) arguments, t < T; reason: values off Z_{t+1} and maps with t ≥ T are never used; monotonicity makes each ϱ_t respect a.e. equality, so it acts on classes; same instances
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, equation (5.18) and Theorem 5.6, proof, p.21 ("It follows that ρT−1,T(Zτ) ⪯ ET−1"; "Then by (5.18) and monotonicity of ϱT−2|FT−2 we obtain")

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_RiskStopTC_IsStoppingFamily
import Definitions.Def_RiskStopTC_nested
import Definitions.Def_RiskStopTC_stoppedRV
import Definitions.Def_RiskStopTC_snell
import Definitions.Def_RiskStopTC_IsStopTimeFrom

open MeasureTheory RiskFunctionals.NestedAVaR

namespace RiskStopTC

/-- **The domination step (5.18).** Pichler, Liu & Shapiro, arXiv:1808.10807v3, Theorem 5.6, proof,
p.21: "1{τ=T−1} ZT−1 + 1{τ=T} ϱT−1|FT−1(ZT) ⪯ max{ZT−1, ϱT−1|FT−1(ET)} = ET−1. (5.18) It follows
that ρT−1,T(Zτ) ⪯ ET−1." and, for `m = T − 2`, "Then by (5.18) and monotonicity of ϱT−2|FT−2 we
obtain ρT−2,T(Zτ) ⪯ … ⪯ max{ZT−2, ϱT−2|FT−2(ET−1)} = ET−2."

For `m < T` and `τ ∈ 𝔗_m`: if `ρ_{m+1,T}(Z_{τ∨(m+1)}) ⪯ E_{m+1}`, then `ρ_{m,T}(Z_τ) ⪯ E_m`.

**Formalization Note.** `E = snell ϱ Z T` and `τ ∨ (m+1)` is `fun ω => max (τ ω) (m+1)`. The
paper prints `m = T − 1` and `m = T − 2`; the statement is the induction step for every `m < T`. -/
theorem eq_5_18 {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (hϱ : IsStoppingFamily ℱ P p T ϱ)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ t ≤ T, IsLp (ℱ t) P p (Z t))
    (m : ℕ) (hm : m < T) (τ : Ω → WithTop ℕ) (hτ : IsStopTimeFrom ℱ T m τ)
    (hstep : nested ϱ (m + 1) T
        (stoppedRV Z (fun ω => max (τ ω) ((m + 1 : ℕ) : WithTop ℕ)) T)
      ≤ᵐ[P] snell ϱ Z T (m + 1)) :
    nested ϱ m T (stoppedRV Z τ T) ≤ᵐ[P] snell ϱ Z T m := by sorry

end RiskStopTC
