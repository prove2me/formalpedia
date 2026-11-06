-- Prove2me | Theorems.Thm_ReflectedBSDE_StoppingControl_stopping_lower_bound
-- name    : ReflectedBSDE.StoppingControl.stopping_lower_bound
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T04:01:57.696203+00:00
-- url     : https://prove2.me/theorems/00b7db80-7b16-4298-99b2-496be13c778d
-- title:
--   Theorem 7.2 (proof) — the stopping time $D_t$ is optimal against every control: $Y_t\le E[\Phi(t,D_t,\beta,\gamma)\mid\mathcal F_t]$
-- statement:
--   Let $B$ be a standard $d$-dimensional Brownian motion on a probability space $(\Omega,\mathcal F,P)$ with augmented natural filtration $(\mathcal F_t)$. Let the data $(\xi,f,S)$ satisfy the standing assumptions (i)–(iv) of §2 with $S_T\le\xi$ a.s., let $S\in\mathcal S^2$, let $f$ be Lipschitz in $(y,z)$ (iii), and let $f(\omega,t,\cdot,\cdot)$ be concave on $\mathbb R\times\mathbb R^d$ for each $(\omega,t)$, $t\le T$. Let $F(t,\beta,\gamma)=\sup_{(y,z)}[f(t,y,z)-\beta y-\langle\gamma,z\rangle]$ be the conjugate of $f$, and let $\mathcal A$ be the class of bounded progressively measurable processes $(\beta,\gamma)$ with $E\int_0^T F(t,\beta_t,\gamma_t)^2\,dt<\infty$. For each $(\beta,\gamma)\in\mathcal A$ let $J^{\beta,\gamma}$ be continuous Itô integrals $\int_0^\cdot\gamma^j_s\,dB^j_s$, which define
--   $$\Gamma^{\beta,\gamma}_{t,s}=\exp\Big(\int_t^s\beta_r\,dr+\int_t^s\gamma_r\,dB_r-\tfrac12\int_t^s|\gamma_r|^2\,dr\Big),$$
--   the solution of $d\Gamma_{t,s}=\Gamma_{t,s}(\beta_s\,ds+(\gamma_s,dB_s))$, $\Gamma_{t,t}=1$, and let
--   $$\Phi(t,v,\beta,\gamma)=\Gamma^{\beta,\gamma}_{t,v}\big[S_v1_{\{v<T\}}+\xi1_{\{v=T\}}\big]+\int_t^v\Gamma^{\beta,\gamma}_{t,s}F(s,\beta_s,\gamma_s)\,ds$$
--   be the payoff of Theorem 7.2, for $t\in[0,T]$ and $v\in\mathcal T_t$ (stopping times with $t\le v\le T$). Let $(Y,Z,K)$ be the solution of the reflected BSDE with coefficient $f$, terminal value $\xi$ and obstacle $S$.
--
--   Then for every $t\in[0,T]$ there is a stopping time $v\in\mathcal T_t$ — namely $D_t=\inf\{t\le u\le T:\ Y_u=S_u\}\wedge T$ — such that for every $(\beta,\gamma)\in\mathcal A$,
--   $$Y_t\le E\big[\Phi(t,v,\beta,\gamma)\mid\mathcal F_t\big]\quad\text{a.s.}$$
--
--   This is the half of the saddle-point property of $\big((\beta^*,\gamma^*),D_t\big)$ in the proof of Theorem 7.2 that concerns the stopping player: stopping at $D_t$ guarantees at least $Y_t$ against every control, which yields $Y_t\le\operatorname{ess\,sup}_{v}\operatorname{ess\,inf}_{(\beta,\gamma)}E[\Phi(t,v,\beta,\gamma)\mid\mathcal F_t]$.
--
--   **Formalization Note** The statement asserts existence of a suitable $v\in\mathcal T_t$; the source's choice is $D_t$.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), pp. 724-725, Section 7 (Proposition 7.1, Theorem 7.2 and its proof), https://doi.org/10.1214/aop/1024404416

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MultiperiodRisk_Bellman_EssInf
import Definitions.Def_ReflectedBSDE_StoppingControl_Setting
import Definitions.Def_ReflectedBSDE_StoppingControl_Control

namespace ReflectedBSDE.StoppingControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Proof of Theorem 7.2 (El Karoui et al. 1997, p. 725): the stopping time
`D_t = inf{t ≤ u ≤ T ; Y_u = S_u} ∧ T` is optimal against every control. Let the data
`(ξ, f, S)` satisfy (i)–(iv) with `S ∈ 𝒮²`, `f` Lipschitz and concave in `(y, z)`, let
`(Y, Z, K)` solve the reflected BSDE with coefficient `f`, and for each `(β, γ) ∈ 𝒜` let
`J^{β,γ}` be continuous Itô integrals of `γ`. Then for every `t ∈ [0, T]` there is a stopping
time `v ∈ 𝒯_t` (namely `D_t`) with `Y_t ≤ E[Φ(t, v, β, γ) | 𝓕_t]` a.s. for every
`(β, γ) ∈ 𝒜`. -/
theorem stopping_lower_bound {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : Peng1990.SMP.IsStdBrownian P B)
    (T : ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : StandingData (augFiltration hB) P T ξ f S)
    (hLip : ∃ K : ℝ, IsLipschitzCoeff P T f K)
    (hS2 : InS2 (augFiltration hB) P T S)
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (hsol : IsRBSDESolution (augFiltration hB) P T B ξ f S Y Z K)
    (J : Control Ω d → Fin d → ℝ≥0 → Ω → ℝ)
    (hJ : ∀ c ∈ admissible (augFiltration hB) P T f,
      IsContItoIntegral (augFiltration hB) P T B c.2 (J c)) :
    ∀ t ≤ T, ∃ v ∈ stoppingTimesFrom (augFiltration hB) T t,
      ∀ c ∈ admissible (augFiltration hB) P T f,
        Y t ≤ᵐ[P] P[payoff T ξ f S c (J c) t v | augFiltration hB t] := by sorry

end ReflectedBSDE.StoppingControl
