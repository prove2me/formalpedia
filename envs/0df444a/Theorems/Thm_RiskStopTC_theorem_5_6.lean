-- Prove2me | Theorems.Thm_RiskStopTC_theorem_5_6
-- name    : RiskStopTC.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:19.466791+00:00
-- url     : https://prove2.me/theorems/a82c8a21-c31c-410f-a8ed-e48c51949fc2
-- title:
--   Theorem 5.6 (corrected: strict monotonicity in (iii)) — the nested-risk Snell envelope is the optimal stopping value, attained by $\tau^*_m$
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space with a filtration $\mathcal F_0\subset\cdots\subset\mathcal F_T$, $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathcal F_T=\mathcal F$, and $\mathcal Z_t=L^p(\Omega,\mathcal F_t,P)$ for a fixed $p\in[1,\infty]$. Relations between random variables hold $P$-almost surely.
--
--   Let $\varrho_{t|\mathcal F_t}:\mathcal Z_{t+1}\to\mathcal Z_t$, $t=0,\dots,T-1$, be monotone translation equivariant mappings with the local property (5.17), and let $\rho_{s,t}$ be the nested functionals (5.1), with $\rho_{m,m}=\mathrm{id}$. Let $Z_t\in\mathcal Z_t$ for $t=0,\dots,T$, let $E$ be the Snell envelope (5.14), $\tau^*_m$ the stopping times (5.16), $\mathfrak T_m$ the stopping times $\tau\ge m$, and $\mathfrak v_m$ the optimal value of
--   $$\max_{\tau\in\mathfrak T_m}\rho_{0,T}(Z_\tau).\tag{5.15}$$
--   Then for every $m=0,\dots,T$:
--
--   1. $\tau^*_m\in\mathfrak T_m$;
--   2. (i) $E_m\succeq\rho_{m,T}(Z_\tau)$ for all $\tau\in\mathfrak T_m$, and $E_m=\rho_{m,T}(Z_{\tau^*_m})$;
--   3. (ii) $\tau^*_m$ is optimal for (5.15): $\rho_{0,T}(Z_{\tau^*_m})$ is the greatest value of $\rho_{0,T}(Z_\tau)$ over $\tau\in\mathfrak T_m$;
--   4. (iii) if moreover every $\varrho_t$ is **strictly monotone**, then every optimal stopping time $\hat\tau\in\mathfrak T_m$ for (5.15) satisfies $\hat\tau\succeq\tau^*_m$ almost surely;
--   5. (iv) $\mathfrak v_m=\rho_{0,m}(E_m)$; in particular $\mathfrak v_0=E_0$.
--
--   The theorem extends the classical Snell envelope characterization of optimal stopping from expectations to nested (time-consistent) risk functionals built from arbitrary monotone, translation equivariant, local one-step mappings: the dynamic programming recursion (5.14) solves the risk-averse stopping problem from every starting date, and the first time the envelope meets the reward is optimal.
--
--   Differences from the source:
--   - correction: (iii) for monotone ϱ_t: an optimal τ̂ for (5.15) satisfies τ̂ ⪰ τ*_m → (iii) assumes in addition that every ϱ_t, t < T, is strictly monotone (Definition 3.4); reason: as printed (iii) is false: T = 2, Ω = {a₁, a₂, b₁, b₂} uniform, F₁ = σ({a₁,a₂},{b₁,b₂}), F₂ = 2^Ω, ϱ₀ = ess sup, ϱ₁ = E[·|F₁], Z₀ = 0, Z₁ = 10·1_a, Z₂ = 2·1_b; then τ*₀ = 1 on a, 2 on b, while τ̂ ≡ 1 attains 𝔳₀ = 10 and τ̂ < τ*₀ on b, of probability 1/2; every hypothesis of Theorem 5.6 holds
--   - reading: (iv) 𝔳_m = ϱ_{0,m}(E_m) → 𝔳_m = ρ_{0,m}(E_m) (nested functional); reason: ϱ_{0,m} is defined nowhere (the one-step ϱ carry one index); p.20 uses ρ_{0,m} three lines above ('ρ0,T(Zτ) = ρ0,m(ρm,T(Zτ))')
--   - encoding: (iv) in two cases: 𝔳_m = ϱ_{0,m}(E_m) for m = 1, …, T, and 𝔳_0 = E_0 → one formula 𝔳_m = ρ_{0,m}(E_m) for m = 0, …, T, with ρ_{0,0} = id; reason: at m = 0 the formula is 𝔳_0 = E_0; same statement
--   - encoding: 'the stopping time τ*_m' (implicit claim that τ*_m ∈ 𝔗_m) → explicit conjunct IsStopTimeFrom ℱ T m τ*_m; reason: the theorem calls τ*_m a stopping time in 𝔗_m; making the claim explicit changes no instance
--   - encoding: real values ρ_{0,T}(Z_τ) and 𝔳_m; 'optimal for (5.15)' → ∫ ρ_{0,T}(Z_τ) dP (stopValue); 𝔳_m as sSup (optValue); (ii) as IsGreatest; τ̂ optimal as ∀ τ ∈ 𝔗_m, value τ ≤ value τ̂; reason: F_0 is trivial, so ρ_{0,·}(·) is constant and equals its integral; IsGreatest makes the max attained, so sSup is the max; same instances
--   - encoding: Z_t = L^p(Ω, F_t, P) as classes of a.e.-equal functions; ⪯ and = almost surely → functions Ω → ℝ with an F_t-measurable representative in L^p (IsLp (ℱ t) P p); relations ≤ᵐ[P] and =ᵐ[P]; reason: every class has such a representative; Lean convention; same instances
--   - encoding: stopping times τ : Ω → {0, …, T} with {τ = t} ∈ F_t; 𝔗_m = {τ ∈ 𝔗 : τ ≥ m} → IsBddStoppingTime ℱ T τ (Mathlib IsStoppingTime, values in WithTop ℕ, τ ≤ T everywhere) and m ≤ τ everywhere (IsStopTimeFrom); reason: in discrete time {τ ≤ t} ∈ F_t for all t is equivalent to {τ = t} ∈ F_t for all t; same instances
--   - encoding: monotone translation equivariant mappings ϱ_t|F_t : Z_{t+1} → Z_t with (5.17), t = 0, …, T − 1 → one family ϱ : ℕ → (Ω → ℝ) → Ω → ℝ with IsStoppingFamily (maps-to, monotone, translation equivariant, (5.17)) on IsLp (ℱ (t+1)) arguments, t < T; reason: values off Z_{t+1} and maps with t ≥ T are never used; monotonicity makes each ϱ_t respect a.e. equality, so it acts on classes; same instances
--   - encoding: ρ_{s,t} for 0 ≤ s < t ≤ T, and ρ_{T,T}(Z_T) ≡ Z_T (footnote 10) → nested ϱ s t, with ρ_{t,t} = id for every t; reason: the paper fixes ρ_{T,T} = id; the identity at other diagonal indices is used only where the statement reads as the paper's at s = t
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, Theorem 5.6, p.20

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
import Definitions.Def_RiskStopTC_stopValue
import Definitions.Def_RiskStopTC_optValue

open MeasureTheory RiskFunctionals.NestedAVaR

namespace RiskStopTC

/-- **Theorem 5.6 (corrected: strict monotonicity in (iii)).** Pichler, Liu & Shapiro, *Risk averse
stochastic programming: time consistency and optimal stopping*, arXiv:1808.10807v3, Theorem 5.6,
p.20: "Let ϱt|Ft : Zt+1 → Zt, t = 0, . . . , T − 1, be monotone translation equivariant mappings
possessing property (5.17) and ρs,t, 0 ≤ s < t ≤ T, be the corresponding nested functionals defined
in (5.1). Then for (Z0, . . . , ZT) ∈ Z0,T the following holds: (i) for m = 0, . . . , T, and τ∗m
defined in (5.16), Em ⪰ ρm,T(Zτ), ∀τ ∈ 𝔗m, Em = ρm,T(Zτ∗m), (ii) the stopping time τ∗m is optimal
for the problem (5.15), (iii) if τ̂m is an optimal stopping time for the problem (5.15), then
τ̂m ⪰ τ∗m, (iv) 𝔳m = ϱ0,m(Em), m = 1, . . . , T, and 𝔳0 = E0."

Setting (§2, p.3): `(Ω, F, P)` a probability space, `F_0 ⊂ ⋯ ⊂ F_T` with `F_0 = {∅, Ω}`,
`F_T = F`, `Z_t = L^p(Ω, F_t, P)` for some `p ∈ [1, ∞]`. For every `m ≤ T`:
* (0) `τ*_m ∈ 𝔗_m` ("the stopping time τ*_m");
* (i) `ρ_{m,T}(Z_τ) ⪯ E_m` for all `τ ∈ 𝔗_m`, and `E_m = ρ_{m,T}(Z_{τ*_m})` a.s.;
* (ii) `ρ_{0,T}(Z_{τ*_m})` is the greatest value of (5.15) over `𝔗_m`;
* (iii) (corrected) if every `ϱ_t` is strictly monotone, every maximizer `τ̂ ∈ 𝔗_m` of (5.15)
  (written `τh`) satisfies `τ*_m ≤ τ̂` a.s.;
* (iv) `𝔳_m = ρ_{0,m}(E_m)` (for `m = 0`: `ρ_{0,0} = id`, so `𝔳_0 = E_0`).

**Formalization Note.**
* Random variables are functions `Ω → ℝ` with a.s. relations; `Z_t`-membership is `IsLp (ℱ t) P p`.
* The one-step family `ϱ : ℕ → (Ω → ℝ) → Ω → ℝ` is constrained only on `Z_{t+1}` and only for
  `t < T` (`IsStoppingFamily`).
* `ρ_{m,m} = id` for every `m` (the paper defines `ρ_{T,T}`; the case `m = 0` of (iv) uses `ρ_{0,0}`).
* `Z_τ` is the paper's sum `∑_{t≤T} 1{τ=t} Z_t` (2.4).
* Stopping times are `IsBddStoppingTime ℱ T τ` with values in `WithTop ℕ`; `𝔗_m` has `m ≤ τ`
  everywhere (`IsStopTimeFrom`).
* Real values are `∫ · ∂P` of `F_0`-measurable (hence constant) functions (`stopValue`); `𝔳_m` is
  an `sSup` (`optValue`), made non-junk by the `IsGreatest` of (ii).
* The strict order `≺` is `≤ᵐ ∧ ¬ =ᵐ`.
* Clause (iii) as printed is false for monotone mappings: `T = 2`, four equally likely points,
  `ϱ_0 = ess sup`, `ϱ_1 = E[· | F_1]`; strict monotonicity of every `ϱ_t` is assumed for (iii)
  only. The printed `ϱ0,m` in (iv) is read as the nested `ρ_{0,m}`. -/
theorem theorem_5_6 {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (hϱ : IsStoppingFamily ℱ P p T ϱ)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ t ≤ T, IsLp (ℱ t) P p (Z t)) :
    ∀ m ≤ T,
      IsStopTimeFrom ℱ T m (tauStar ϱ Z T m) ∧
      (∀ τ, IsStopTimeFrom ℱ T m τ → nested ϱ m T (stoppedRV Z τ T) ≤ᵐ[P] snell ϱ Z T m) ∧
      snell ϱ Z T m =ᵐ[P] nested ϱ m T (stoppedRV Z (tauStar ϱ Z T m) T) ∧
      IsGreatest (stopValue P ϱ Z T '' {τ | IsStopTimeFrom ℱ T m τ})
        (stopValue P ϱ Z T (tauStar ϱ Z T m)) ∧
      (IsStrictlyMonotoneFamily ℱ P p T ϱ → ∀ τh, IsStopTimeFrom ℱ T m τh →
        (∀ τ, IsStopTimeFrom ℱ T m τ → stopValue P ϱ Z T τ ≤ stopValue P ϱ Z T τh) →
        ∀ᵐ ω ∂P, tauStar ϱ Z T m ω ≤ τh ω) ∧
      optValue ℱ P ϱ Z T m = ∫ ω, nested ϱ 0 m (snell ϱ Z T m) ω ∂P := by sorry

end RiskStopTC
