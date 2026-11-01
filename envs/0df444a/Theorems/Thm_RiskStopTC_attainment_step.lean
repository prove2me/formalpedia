-- Prove2me | Theorems.Thm_RiskStopTC_attainment_step
-- name    : RiskStopTC.attainment_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:06.582349+00:00
-- url     : https://prove2.me/theorems/b7b16d5a-c414-4553-b3e0-fe3bbaffadf0
-- title:
--   Theorem 5.6, proof, p.21 — the attainment step: $E_{m+1}=\rho_{m+1,T}(Z_{\tau^*_{m+1}})$ implies $E_m=\rho_{m,T}(Z_{\tau^*_m})$
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space with a filtration $\mathcal F_0\subset\cdots\subset\mathcal F_T$, $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathcal F_T=\mathcal F$, and $\mathcal Z_t=L^p(\Omega,\mathcal F_t,P)$ for a fixed $p\in[1,\infty]$. Relations between random variables hold $P$-almost surely.
--
--   Let $\varrho_t$, $t<T$, be monotone, translation equivariant mappings $\mathcal Z_{t+1}\to\mathcal Z_t$ with (5.17), let $Z_t\in\mathcal Z_t$, let $E$ be the Snell envelope (5.14) and $\tau^*_m$ the stopping times (5.16). Let $m<T$. If
--   $$E_{m+1}=\rho_{m+1,T}\big(Z_{\tau^*_{m+1}}\big)\quad\text{a.s.},$$
--   then
--   $$E_m=\rho_{m,T}\big(Z_{\tau^*_m}\big)\quad\text{a.s.}$$
--
--   The paper argues by the case split $\{Z_m\ge\varrho_m(E_{m+1})\}$, where $E_m=Z_m$ and $\tau^*_m=m$, and its complement, where $E_m=\varrho_m(E_{m+1})$ and $\tau^*_m=\tau^*_{m+1}$; it writes the cases out for $m=T-1$ and $m=T-2$. Iterating the step gives the second half of clause (i) of Theorem 5.6.
--
--   Differences from the source:
--   - generalization: the case analysis for m = T − 1 and m = T − 2 → the induction step for every m < T, with hypothesis E_{m+1} = ρ_{m+1,T}(Z_{τ*_{m+1}}) a.s.; reason: at m = T − 1 the hypothesis is E_T = Z_T, true, and the conclusion is the page's; the general m is the step left to 'going backwards in time'
--   - encoding: Z_t = L^p(Ω, F_t, P) as classes of a.e.-equal functions; ⪯ and = almost surely → functions Ω → ℝ with an F_t-measurable representative in L^p (IsLp (ℱ t) P p); relations ≤ᵐ[P] and =ᵐ[P]; reason: every class has such a representative; Lean convention; same instances
--   - encoding: monotone translation equivariant mappings ϱ_t|F_t : Z_{t+1} → Z_t with (5.17), t = 0, …, T − 1 → one family ϱ : ℕ → (Ω → ℝ) → Ω → ℝ with IsStoppingFamily (maps-to, monotone, translation equivariant, (5.17)) on IsLp (ℱ (t+1)) arguments, t < T; reason: values off Z_{t+1} and maps with t ≥ T are never used; monotonicity makes each ϱ_t respect a.e. equality, so it acts on classes; same instances
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, Theorem 5.6, proof, p.21 ("Conditional on the event {ZT−1 ≥ ϱT−1|FT−1(ET)} …")

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_RiskStopTC_IsStoppingFamily
import Definitions.Def_RiskStopTC_nested
import Definitions.Def_RiskStopTC_stoppedRV
import Definitions.Def_RiskStopTC_snell
import Definitions.Def_RiskStopTC_tauStar

open MeasureTheory RiskFunctionals.NestedAVaR

namespace RiskStopTC

/-- **The attainment step.** Pichler, Liu & Shapiro, arXiv:1808.10807v3, Theorem 5.6, proof, p.21:
"Conditional on the event {ZT−1 ≥ ϱT−1|FT−1(ET)} we have: ET−1 = ZT−1 and τ∗T−1 = T − 1, and
ρT−1,T(Zτ∗T−1) = ϱT−1|FT−1(ZT−1) = ZT−1 = ET−1, and τ∗T−1 is optimal for the corresponding problem
(5.15). Otherwise conditional on the event {ZT−1 < ϱT−1|FT−1(ZT)}, we have that
ET−1 = ϱT−1|FT−1(ZT), and τ∗T−1 = T is optimal for the corresponding problem (5.15)."

For `m < T`: if `E_{m+1} = ρ_{m+1,T}(Z_{τ*_{m+1}})` a.s., then `E_m = ρ_{m,T}(Z_{τ*_m})` a.s.

**Formalization Note.** `E = snell ϱ Z T` (5.14) and `τ*_m = tauStar ϱ Z T m` (5.16). The paper
prints `m = T − 1` and `m = T − 2`; the statement is the induction step for every `m < T`. -/
theorem attainment_step {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (hϱ : IsStoppingFamily ℱ P p T ϱ)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ t ≤ T, IsLp (ℱ t) P p (Z t))
    (m : ℕ) (hm : m < T)
    (hstep : snell ϱ Z T (m + 1) =ᵐ[P]
      nested ϱ (m + 1) T (stoppedRV Z (tauStar ϱ Z T (m + 1)) T)) :
    snell ϱ Z T m =ᵐ[P] nested ϱ m T (stoppedRV Z (tauStar ϱ Z T m) T) := by sorry

end RiskStopTC
