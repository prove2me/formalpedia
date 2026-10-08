-- Prove2me | Theorems.Thm_ReflectedBSDE_StoppingControl_minimax_representation
-- name    : ReflectedBSDE.StoppingControl.minimax_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:51.221934+00:00
-- url     : https://prove2.me/theorems/8954b724-e09b-4f66-8e14-0cec9e431825
-- title:
--   Theorem 7.2 — with a concave coefficient, $Y_t$ is the value of a minimax optimal stopping–control problem
-- statement:
--   Let the data $(\xi,f,S)$ satisfy (i)–(iv), $S_T\le\xi$ a.s. and $S\in\mathcal S^2$, and let $f(\omega,t,\cdot,\cdot)$ be concave on $\mathbb R\times\mathbb R^d$ for each $(\omega,t)$. Let $(Y,Z,K)$ be the solution of the reflected BSDE with coefficient $f$, and for each admissible control $(\beta,\gamma)\in\mathcal A$ let $(Y^{\beta,\gamma},Z^{\beta,\gamma},K^{\beta,\gamma})$ be the solution of the reflected BSDE with the affine coefficient $f^{\beta,\gamma}(t,y,z)=F(t,\beta_t,\gamma_t)+\beta_ty+\langle\gamma_t,z\rangle$. Let
--   $$\Phi(t,v,\beta,\gamma)=\Gamma^{\beta,\gamma}_{t,v}\big[S_v1_{\{v<T\}}+\xi1_{\{v=T\}}\big]+\int_t^v\Gamma^{\beta,\gamma}_{t,s}F(s,\beta_s,\gamma_s)\,ds,$$
--   where $\Gamma^{\beta,\gamma}_{t,\cdot}$ solves $d\Gamma_{t,s}=\Gamma_{t,s}(\beta_s\,ds+(\gamma_s,dB_s))$, $\Gamma_{t,t}=1$. Then for every $t\in[0,T]$:
--
--   1. for each $(\beta,\gamma)\in\mathcal A$, $$Y^{\beta,\gamma}_t=\operatorname*{ess\,sup}_{v\in\mathcal T_t}E[\Phi(t,v,\beta,\gamma)\mid\mathcal F_t];$$
--   2. and
--   $$Y_t=\operatorname*{ess\,inf}_{(\beta,\gamma)\in\mathcal A}Y^{\beta,\gamma}_t=\operatorname*{ess\,inf}_{(\beta,\gamma)\in\mathcal A}\ \operatorname*{ess\,sup}_{v\in\mathcal T_t}E[\Phi(t,v,\beta,\gamma)\mid\mathcal F_t]=\operatorname*{ess\,sup}_{v\in\mathcal T_t}\ \operatorname*{ess\,inf}_{(\beta,\gamma)\in\mathcal A}E[\Phi(t,v,\beta,\gamma)\mid\mathcal F_t].$$
--
--   So $Y_t$ is the value of a game in which one player chooses the stopping time $v$ and the other the control $(\beta,\gamma)$, and the order of play does not matter.
--
--   **Formalization Note** The solutions $(Y^{\beta,\gamma},Z^{\beta,\gamma},K^{\beta,\gamma})$ and continuous Itô integrals $J^{\beta,\gamma}$ of $\gamma$ (which define $\Gamma^{\beta,\gamma}$ in closed form) are given as families indexed by $\mathcal A$; they exist by the existence theorem for reflected BSDEs and the continuity of Itô integrals. $S\in\mathcal S^2$ is added (Remark 3.2) so that $\Phi$ is integrable. Essential suprema and infima are relative to $\mathcal F_t$ and real valued; the third equality also asserts that for each $v\in\mathcal T_t$ the inner essential infimum exists. The closing sentence of the theorem ("the triple $(\beta^*,\gamma^*,D_t)$ is optimal") is not formalized here; the existence of $(\beta^*,\gamma^*)$ is the milestone `optimal_control_exists`.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 725, Theorem 7.2, https://doi.org/10.1214/aop/1024404416

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MultiperiodRisk_Bellman_EssInf
import Definitions.Def_ReflectedBSDE_StoppingControl_Setting
import Definitions.Def_ReflectedBSDE_StoppingControl_Control

namespace ReflectedBSDE.StoppingControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Theorem 7.2 (El Karoui et al. 1997, p. 725). Let `f` be concave in `(y, z)`, `S ∈ 𝒮²`,
`(Y, Z, K)` the solution of the reflected BSDE with coefficient `f`, and for each
`(β, γ) ∈ 𝒜` let `(Y^{β,γ}, Z^{β,γ}, K^{β,γ})` solve the reflected BSDE with the affine
coefficient `f^{β,γ}` and `J^{β,γ}` be continuous Itô integrals of `γ` (defining `Γ^{β,γ}`).
Then for every `t ∈ [0, T]`:
1. `Y^{β,γ}_t = ess sup_{v ∈ 𝒯_t} E[Φ(t, v, β, γ) | 𝓕_t]` for each `(β, γ) ∈ 𝒜`;
2. `Y_t = ess inf_{(β,γ) ∈ 𝒜} Y^{β,γ}_t`;
3. `Y_t = ess inf_{(β,γ) ∈ 𝒜} ess sup_{v ∈ 𝒯_t} E[Φ(t, v, β, γ) | 𝓕_t]`;
4. for each `v ∈ 𝒯_t` the essential infimum `ess inf_{(β,γ) ∈ 𝒜} E[Φ(t, v, β, γ) | 𝓕_t]` exists
   (as a real random variable), and
   `Y_t = ess sup_{v ∈ 𝒯_t} ess inf_{(β,γ) ∈ 𝒜} E[Φ(t, v, β, γ) | 𝓕_t]`. -/
theorem minimax_representation {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
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
      IsContItoIntegral (augFiltration hB) P T B c.2 (J c))
    (Yc : Control Ω d → ℝ≥0 → Ω → ℝ) (Zc : Control Ω d → ℝ≥0 → Ω → Fin d → ℝ)
    (Kc : Control Ω d → ℝ≥0 → Ω → ℝ)
    (hYc : ∀ c ∈ admissible (augFiltration hB) P T f,
      IsRBSDESolution (augFiltration hB) P T B ξ (affineCoeff f c) S (Yc c) (Zc c) (Kc c)) :
    ∀ t ≤ T,
      (∀ c ∈ admissible (augFiltration hB) P T f,
        IsEssSup P (augFiltration hB t)
          {X | ∃ v ∈ stoppingTimesFrom (augFiltration hB) T t,
            X = P[payoff T ξ f S c (J c) t v | augFiltration hB t]}
          (Yc c t)) ∧
      MultiperiodRisk.Bellman.IsEssInf P (augFiltration hB t)
        ((fun c => Yc c t) '' admissible (augFiltration hB) P T f) (Y t) ∧
      MultiperiodRisk.Bellman.IsEssInf P (augFiltration hB t)
        {X | ∃ c ∈ admissible (augFiltration hB) P T f,
          IsEssSup P (augFiltration hB t)
            {X' | ∃ v ∈ stoppingTimesFrom (augFiltration hB) T t,
              X' = P[payoff T ξ f S c (J c) t v | augFiltration hB t]} X}
        (Y t) ∧
      (∀ v ∈ stoppingTimesFrom (augFiltration hB) T t, ∃ X : Ω → ℝ,
        MultiperiodRisk.Bellman.IsEssInf P (augFiltration hB t)
          {X' | ∃ c ∈ admissible (augFiltration hB) P T f,
            X' = P[payoff T ξ f S c (J c) t v | augFiltration hB t]} X) ∧
      IsEssSup P (augFiltration hB t)
        {X | ∃ v ∈ stoppingTimesFrom (augFiltration hB) T t,
          MultiperiodRisk.Bellman.IsEssInf P (augFiltration hB t)
            {X' | ∃ c ∈ admissible (augFiltration hB) P T f,
              X' = P[payoff T ξ f S c (J c) t v | augFiltration hB t]} X}
        (Y t) := by sorry

end ReflectedBSDE.StoppingControl
