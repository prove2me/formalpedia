-- Prove2me | Theorems.Thm_ReflectedBSDE_StoppingControl_payoff_integrable
-- name    : ReflectedBSDE.StoppingControl.payoff_integrable
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T04:01:38.344341+00:00
-- url     : https://prove2.me/theorems/ec7fbcb1-7812-4583-9be6-08cdffd839e1
-- title:
--   §7 — the payoffs $\Phi(t,v,\beta,\gamma)$ and $\Gamma^{\beta,\gamma}_{0,t}\Phi(t,v,\beta,\gamma)$ are integrable
-- statement:
--   Let $B$ be a standard $d$-dimensional Brownian motion on a probability space $(\Omega,\mathcal F,P)$ with augmented natural filtration $(\mathcal F_t)$. Let the data $(\xi,f,S)$ satisfy the standing assumptions (i)–(iv) of §2 with $S_T\le\xi$ a.s., let $S\in\mathcal S^2$, let $f$ be Lipschitz in $(y,z)$ (iii), and let $f(\omega,t,\cdot,\cdot)$ be concave on $\mathbb R\times\mathbb R^d$ for each $(\omega,t)$, $t\le T$. Let $F(t,\beta,\gamma)=\sup_{(y,z)}[f(t,y,z)-\beta y-\langle\gamma,z\rangle]$ be the conjugate of $f$, and let $\mathcal A$ be the class of bounded progressively measurable processes $(\beta,\gamma)$ with $E\int_0^T F(t,\beta_t,\gamma_t)^2\,dt<\infty$. For each $(\beta,\gamma)\in\mathcal A$ let $J^{\beta,\gamma}$ be continuous Itô integrals $\int_0^\cdot\gamma^j_s\,dB^j_s$, which define
--   $$\Gamma^{\beta,\gamma}_{t,s}=\exp\Big(\int_t^s\beta_r\,dr+\int_t^s\gamma_r\,dB_r-\tfrac12\int_t^s|\gamma_r|^2\,dr\Big),$$
--   the solution of $d\Gamma_{t,s}=\Gamma_{t,s}(\beta_s\,ds+(\gamma_s,dB_s))$, $\Gamma_{t,t}=1$, and let
--   $$\Phi(t,v,\beta,\gamma)=\Gamma^{\beta,\gamma}_{t,v}\big[S_v1_{\{v<T\}}+\xi1_{\{v=T\}}\big]+\int_t^v\Gamma^{\beta,\gamma}_{t,s}F(s,\beta_s,\gamma_s)\,ds$$
--   be the payoff of Theorem 7.2, for $t\in[0,T]$ and $v\in\mathcal T_t$ (stopping times with $t\le v\le T$).
--
--   Then for every $t\in[0,T]$, every $(\beta,\gamma)\in\mathcal A$ and every $v\in\mathcal T_t$:
--
--   1. $\Phi(t,v,\beta,\gamma)$ is integrable;
--   2. $\Gamma^{\beta,\gamma}_{0,t}\,\Phi(t,v,\beta,\gamma)=\Gamma_v\big[S_v1_{\{v<T\}}+\xi1_{\{v=T\}}\big]+\int_t^v\Gamma_sF(s,\beta_s,\gamma_s)\,ds$ (with $\Gamma=\Gamma^{\beta,\gamma}_{0,\cdot}$, the payoff of Proposition 7.1) is integrable.
--
--   These integrability facts are used implicitly in §7 whenever conditional expectations of the payoffs are taken (they are the reason the assumption $S\in\mathcal S^2$ of Remark 3.2 is imposed); they allow passing between the representations of Proposition 7.1 and Theorem 7.2 by pulling the $\mathcal F_t$-measurable factor $\Gamma_{0,t}$ out of $E[\,\cdot\mid\mathcal F_t]$.
--
--   **Formalization Note** $F$ is read as a real number (value $0$ where it is $+\infty$, a $dt\times dP$-null set for $(\beta,\gamma)\in\mathcal A$); the Itô integrals are given as a family indexed by $\mathcal A$, as in the goal theorem `minimax_representation`.
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

/-- Integrability of the payoffs of §7 (El Karoui et al. 1997, pp. 724–725; Remark 3.2 and the
standing assumption `S ∈ 𝒮²`). Let the data `(ξ, f, S)` satisfy (i)–(iv) with `S ∈ 𝒮²`, `f`
Lipschitz and concave in `(y, z)`, and for each `(β, γ) ∈ 𝒜` let `J^{β,γ}` be continuous Itô
integrals of `γ`. Then for every `t ∈ [0, T]`, every `(β, γ) ∈ 𝒜` and every `v ∈ 𝒯_t`, the
payoff `Φ(t, v, β, γ)` of Theorem 7.2 is integrable, and so is
`Γ^{β,γ}_{0,t} Φ(t, v, β, γ) = Γ_v[S_v 1_{v<T} + ξ 1_{v=T}] + ∫ₜᵛ Γ_s F(s, β_s, γ_s) ds`
(the payoff of Proposition 7.1, with `Γ = Γ^{β,γ}_{0,·}`). -/
theorem payoff_integrable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : Peng1990.SMP.IsStdBrownian P B)
    (T : ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : StandingData (augFiltration hB) P T ξ f S)
    (hLip : ∃ K : ℝ, IsLipschitzCoeff P T f K)
    (hS2 : InS2 (augFiltration hB) P T S)
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (J : Control Ω d → Fin d → ℝ≥0 → Ω → ℝ)
    (hJ : ∀ c ∈ admissible (augFiltration hB) P T f,
      IsContItoIntegral (augFiltration hB) P T B c.2 (J c)) :
    ∀ t ≤ T, ∀ c ∈ admissible (augFiltration hB) P T f,
      ∀ v ∈ stoppingTimesFrom (augFiltration hB) T t,
        Integrable (payoff T ξ f S c (J c) t v) P ∧
        Integrable (fun ω => linGamma c.1 c.2 (J c) 0 t ω * payoff T ξ f S c (J c) t v ω) P := by sorry

end ReflectedBSDE.StoppingControl
