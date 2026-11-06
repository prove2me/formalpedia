-- Prove2me | Theorems.Thm_ReflectedBSDE_StoppingControl_inner_essInf_exists
-- name    : ReflectedBSDE.StoppingControl.inner_essInf_exists
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T04:02:07.376111+00:00
-- url     : https://prove2.me/theorems/ca649010-3d84-401f-96aa-b1de0d249c65
-- title:
--   Theorem 7.2 — the inner essential infimum $\operatorname{ess\,inf}_{(\beta,\gamma)\in\mathcal A}E[\Phi(t,v,\beta,\gamma)\mid\mathcal F_t]$ is real valued
-- statement:
--   Let $B$ be a standard $d$-dimensional Brownian motion on a probability space $(\Omega,\mathcal F,P)$ with augmented natural filtration $(\mathcal F_t)$. Let the data $(\xi,f,S)$ satisfy the standing assumptions (i)–(iv) of §2 with $S_T\le\xi$ a.s., let $S\in\mathcal S^2$, let $f$ be Lipschitz in $(y,z)$ (iii), and let $f(\omega,t,\cdot,\cdot)$ be concave on $\mathbb R\times\mathbb R^d$ for each $(\omega,t)$, $t\le T$. Let $F(t,\beta,\gamma)=\sup_{(y,z)}[f(t,y,z)-\beta y-\langle\gamma,z\rangle]$ be the conjugate of $f$, and let $\mathcal A$ be the class of bounded progressively measurable processes $(\beta,\gamma)$ with $E\int_0^T F(t,\beta_t,\gamma_t)^2\,dt<\infty$. For each $(\beta,\gamma)\in\mathcal A$ let $J^{\beta,\gamma}$ be continuous Itô integrals $\int_0^\cdot\gamma^j_s\,dB^j_s$, which define
--   $$\Gamma^{\beta,\gamma}_{t,s}=\exp\Big(\int_t^s\beta_r\,dr+\int_t^s\gamma_r\,dB_r-\tfrac12\int_t^s|\gamma_r|^2\,dr\Big),$$
--   the solution of $d\Gamma_{t,s}=\Gamma_{t,s}(\beta_s\,ds+(\gamma_s,dB_s))$, $\Gamma_{t,t}=1$, and let
--   $$\Phi(t,v,\beta,\gamma)=\Gamma^{\beta,\gamma}_{t,v}\big[S_v1_{\{v<T\}}+\xi1_{\{v=T\}}\big]+\int_t^v\Gamma^{\beta,\gamma}_{t,s}F(s,\beta_s,\gamma_s)\,ds$$
--   be the payoff of Theorem 7.2, for $t\in[0,T]$ and $v\in\mathcal T_t$ (stopping times with $t\le v\le T$).
--
--   Then for every $t\in[0,T]$ and every $v\in\mathcal T_t$ the family
--   $$\big\{E[\Phi(t,v,\beta,\gamma)\mid\mathcal F_t]\ :\ (\beta,\gamma)\in\mathcal A\big\}$$
--   has a real-valued essential infimum relative to $\mathcal F_t$, i.e. an $\mathcal F_t$-measurable real random variable that is a.s. below every member of the family and a.s. above every $\mathcal F_t$-measurable real lower bound of the family.
--
--   This is the existence of the inner essential infimum appearing in the last expression of Theorem 7.2, $\operatorname{ess\,sup}_{v\in\mathcal T_t}\operatorname{ess\,inf}_{(\beta,\gamma)\in\mathcal A}E[\Phi(t,v,\beta,\gamma)\mid\mathcal F_t]$, as a real random variable.
--
--   **Formalization Note** Essential infima are relative to $\mathcal F_t$ and real valued (the published predicate `MultiperiodRisk.Bellman.IsEssInf`); this is item 4 of the formal goal theorem `minimax_representation`.
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

/-- Theorem 7.2 (El Karoui et al. 1997, p. 725), the inner essential infimum of the
sup–inf expression is a real random variable. Let the data `(ξ, f, S)` satisfy (i)–(iv) with
`S ∈ 𝒮²`, `f` Lipschitz and concave in `(y, z)`, and for each `(β, γ) ∈ 𝒜` let `J^{β,γ}` be
continuous Itô integrals of `γ`. Then for every `t ∈ [0, T]` and every `v ∈ 𝒯_t`, the family
`{E[Φ(t, v, β, γ) | 𝓕_t] : (β, γ) ∈ 𝒜}` has a real-valued `𝓕_t`-essential infimum. -/
theorem inner_essInf_exists {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : Peng1990.SMP.IsStdBrownian P B)
    (T : ℝ≥0) (ξ : Ω → ℝ) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (hdata : StandingData (augFiltration hB) P T ξ f S)
    (hLip : ∃ K : ℝ, IsLipschitzCoeff P T f K)
    (hS2 : InS2 (augFiltration hB) P T S)
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (J : Control Ω d → Fin d → ℝ≥0 → Ω → ℝ)
    (hJ : ∀ c ∈ admissible (augFiltration hB) P T f,
      IsContItoIntegral (augFiltration hB) P T B c.2 (J c)) :
    ∀ t ≤ T, ∀ v ∈ stoppingTimesFrom (augFiltration hB) T t, ∃ X : Ω → ℝ,
      MultiperiodRisk.Bellman.IsEssInf P (augFiltration hB t)
        {X' | ∃ c ∈ admissible (augFiltration hB) P T f,
          X' = P[payoff T ξ f S c (J c) t v | augFiltration hB t]} X := by sorry

end ReflectedBSDE.StoppingControl
