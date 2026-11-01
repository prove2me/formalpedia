-- Prove2me | Theorems.Thm_RiskStopTC_strict_step
-- name    : RiskStopTC.strict_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:08.294311+00:00
-- url     : https://prove2.me/theorems/3f344090-20c6-42eb-97a4-f1c344a78a65
-- title:
--   Theorem 5.6, proof, p.21 (corrected: strict monotonicity) — stopping before $\tau^*_m$ with positive probability gives $\rho_{m,T}(Z_{\hat\tau})\prec E_m$
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space with a filtration $\mathcal F_0\subset\cdots\subset\mathcal F_T$, $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathcal F_T=\mathcal F$, and $\mathcal Z_t=L^p(\Omega,\mathcal F_t,P)$ for a fixed $p\in[1,\infty]$. Relations between random variables hold $P$-almost surely.
--
--   Let $\varrho_t$, $t<T$, be monotone, translation equivariant mappings $\mathcal Z_{t+1}\to\mathcal Z_t$ with (5.17) that are moreover **strictly monotone** (Definition 3.4). Let $Z_t\in\mathcal Z_t$, let $E$ be the Snell envelope (5.14) and $\tau^*_m$ the stopping times (5.16). Let $m\le T$ and $\hat\tau\in\mathfrak T_m$ with $P(\hat\tau<\tau^*_m)>0$. Then
--   $$\rho_{m,T}(Z_{\hat\tau})\prec E_m,$$
--   that is, $\rho_{m,T}(Z_{\hat\tau})\preceq E_m$ almost surely and $\rho_{m,T}(Z_{\hat\tau})\neq E_m$ as elements of $L^p$.
--
--   Since $E_m=\rho_{m,T}(Z_{\tau^*_m})$ by Theorem 5.6 (i), this says that a stopping time that stops earlier than $\tau^*_m$ with positive probability is not optimal for the conditional problem started at $m$: the assertion (iii) at stage $m$, which the paper claims at each step of its induction ("In both cases the assertion (iii) also holds").
--
--   Differences from the source:
--   - correction: (iii) for monotone ϱ_t: an optimal τ̂ for (5.15) satisfies τ̂ ⪰ τ*_m → (iii) assumes in addition that every ϱ_t, t < T, is strictly monotone (Definition 3.4); reason: as printed (iii) is false: T = 2, Ω = {a₁, a₂, b₁, b₂} uniform, F₁ = σ({a₁,a₂},{b₁,b₂}), F₂ = 2^Ω, ϱ₀ = ess sup, ϱ₁ = E[·|F₁], Z₀ = 0, Z₁ = 10·1_a, Z₂ = 2·1_b; then τ*₀ = 1 on a, 2 on b, while τ̂ ≡ 1 attains 𝔳₀ = 10 and τ̂ < τ*₀ on b, of probability 1/2; every hypothesis of Theorem 5.6 holds
--   - reading: 'the assertion (iii) also holds' for the problem started at T − 1 ('the corresponding problem (5.15)') → contrapositive at stage m, for the conditional objective ρ_{m,T}: P(τ̂ < τ*_m) > 0 implies ρ_{m,T}(Z_τ̂) ≺ E_m; reason: the problem started at stage m has the conditional objective ρ_{m,T}, whose maximum is E_m by (i); given (i), 'τ̂ is not optimal for it' is exactly ρ_{m,T}(Z_τ̂) ≺ E_m
--   - generalization: the step at m = T − 1 (and m = T − 2) → every m ≤ T; reason: the paper proves (iii) by 'going backwards in time'; m = T − 1 is an instance
--   - encoding: Z_t = L^p(Ω, F_t, P) as classes of a.e.-equal functions; ⪯ and = almost surely → functions Ω → ℝ with an F_t-measurable representative in L^p (IsLp (ℱ t) P p); relations ≤ᵐ[P] and =ᵐ[P]; reason: every class has such a representative; Lean convention; same instances
--   - encoding: stopping times τ : Ω → {0, …, T} with {τ = t} ∈ F_t; 𝔗_m = {τ ∈ 𝔗 : τ ≥ m} → IsBddStoppingTime ℱ T τ (Mathlib IsStoppingTime, values in WithTop ℕ, τ ≤ T everywhere) and m ≤ τ everywhere (IsStopTimeFrom); reason: in discrete time {τ ≤ t} ∈ F_t for all t is equivalent to {τ = t} ∈ F_t for all t; same instances
--   - encoding: monotone translation equivariant mappings ϱ_t|F_t : Z_{t+1} → Z_t with (5.17), t = 0, …, T − 1 → one family ϱ : ℕ → (Ω → ℝ) → Ω → ℝ with IsStoppingFamily (maps-to, monotone, translation equivariant, (5.17)) on IsLp (ℱ (t+1)) arguments, t < T; reason: values off Z_{t+1} and maps with t ≥ T are never used; monotonicity makes each ϱ_t respect a.e. equality, so it acts on classes; same instances
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, Theorem 5.6, proof, p.21 ("In both cases the assertion (iii) also holds."); Definition 3.4, p.7 (strictly monotone)

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_RiskStopTC_IsStoppingFamily
import Definitions.Def_RiskStopTC_IsStrictlyMonotoneFamily
import Definitions.Def_RiskStopTC_nested
import Definitions.Def_RiskStopTC_stoppedRV
import Definitions.Def_RiskStopTC_snell
import Definitions.Def_RiskStopTC_tauStar
import Definitions.Def_RiskStopTC_IsStopTimeFrom

open MeasureTheory RiskFunctionals.NestedAVaR

namespace RiskStopTC

/-- **Stopping before τ*_m loses value strictly (corrected).** Pichler, Liu & Shapiro,
arXiv:1808.10807v3, Theorem 5.6, proof, p.21: "In both cases the assertion (iii) also holds."

Assume moreover that every `ϱ_t`, `t < T`, is strictly monotone (Definition 3.4, p.7). For `m ≤ T`
and `τ̂ ∈ 𝔗_m` with `P(τ̂ < τ*_m) > 0`: `ρ_{m,T}(Z_τ̂) ≺ E_m`, i.e. `ρ_{m,T}(Z_τ̂) ⪯ E_m` and
`ρ_{m,T}(Z_τ̂) ≠ E_m`.

**Formalization Note.** The paper's sentence claims clause (iii) at each step of the induction for
monotone mappings; that is false (counterexample in the goal's differences), and strict
monotonicity is the minimal correction. `P(τ̂ < τ*_m) > 0` is `¬ (τ*_m ≤ τ̂ a.s.)`, and `≺` is
`≤ᵐ ∧ ¬ =ᵐ`; `τ̂` is written `τh`. -/
theorem strict_step {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (hϱ : IsStoppingFamily ℱ P p T ϱ)
    (hstrict : IsStrictlyMonotoneFamily ℱ P p T ϱ)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ t ≤ T, IsLp (ℱ t) P p (Z t))
    (m : ℕ) (hm : m ≤ T) (τh : Ω → WithTop ℕ) (hτh : IsStopTimeFrom ℱ T m τh)
    (hlt : ¬ ∀ᵐ ω ∂P, tauStar ϱ Z T m ω ≤ τh ω) :
    nested ϱ m T (stoppedRV Z τh T) ≤ᵐ[P] snell ϱ Z T m ∧
      ¬ nested ϱ m T (stoppedRV Z τh T) =ᵐ[P] snell ϱ Z T m := by sorry

end RiskStopTC
