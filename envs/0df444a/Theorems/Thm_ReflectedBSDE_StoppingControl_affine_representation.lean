-- Prove2me | Theorems.Thm_ReflectedBSDE_StoppingControl_affine_representation
-- name    : ReflectedBSDE.StoppingControl.affine_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:20.963229+00:00
-- url     : https://prove2.me/theorems/d2eb318b-44ea-4212-ba8d-5337e4fd3a33
-- title:
--   Proposition 7.1 — for an affine coefficient, $\Gamma_tY_t$ is the Snell envelope of the discounted payoff
-- statement:
--   Suppose the coefficient is affine in $(y,z)$,
--   $$f(t,y,z)=\delta_t+\beta_ty+\langle\gamma_t,z\rangle,$$
--   where $\delta,\beta,\gamma$ are progressively measurable with values in $\mathbb R\times\mathbb R\times\mathbb R^d$, $E\int_0^T\delta_t^2\,dt<\infty$ and $|\beta_t|+|\gamma_t|\le C$ a.s. for $0\le t\le T$. Let $\Gamma$ be the solution of $d\Gamma_t=\Gamma_t[\beta_t\,dt+(\gamma_t,dB_t)]$, $\Gamma_0=1$. Let $\xi$ and $S$ satisfy (i), (iv), $S_T\le\xi$ a.s., and $S\in\mathcal S^2$, and let $(Y,Z,K)$ be the solution of the reflected BSDE with coefficient $f$. Then for each $0\le t\le T$,
--   $$\Gamma_tY_t=\operatorname*{ess\,sup}_{v\in\mathcal T_t}E\Big[\Gamma_v\xi1_{\{v=T\}}+\Gamma_vS_v1_{\{v<T\}}+\int_t^v\Gamma_s\delta_s\,ds\,\Big|\,\mathcal F_t\Big].$$
--
--   This is the affine case of Theorem 7.2: applied to $f^{\beta,\gamma}$ it gives the stopping-time representation of each $Y^{\beta,\gamma}$.
--
--   **Formalization Note** The paper prints the upper limit of the integral as $u$; it is $v$, as in the proof's last display. "The BSDE with coefficient $f$" is the reflected BSDE. $S\in\mathcal S^2$ is added (Remark 3.2: without loss of generality) so that the payoff is integrable; Lean's conditional expectation of a non-integrable function is $0$. $\Gamma_t=\Gamma_{0,t}$ is the closed-form solution of `ReflectedBSDE.StoppingControl.Control`, built from continuous Itô integrals $J$ of $\gamma$. The essential supremum is relative to $\mathcal F_t$. The data hypothesis records (i), (ii), (iv) and $S_T\le\xi$ for the affine coefficient; (ii) follows from the hypotheses on $\delta,\beta,\gamma$.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 724, Proposition 7.1, https://doi.org/10.1214/aop/1024404416

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MultiperiodRisk_Bellman_EssInf
import Definitions.Def_ReflectedBSDE_StoppingControl_Setting
import Definitions.Def_ReflectedBSDE_StoppingControl_Control

namespace ReflectedBSDE.StoppingControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

/-- Proposition 7.1 (El Karoui et al. 1997, p. 724). For the affine coefficient
`f(t, y, z) = δ_t + β_t y + ⟨γ_t, z⟩` with `δ ∈ ℍ²` and `|β_t| + |γ_t| ≤ C`, and
`Γ_t = Γ_{0,t}` the solution of `dΓ_t = Γ_t[β_t dt + (γ_t, dB_t)]`, `Γ_0 = 1`, the solution of the
reflected BSDE satisfies, for each `t ∈ [0, T]`,
`Γ_t Y_t = ess sup_{v ∈ 𝒯_t} E[Γ_v ξ 1_{v=T} + Γ_v S_v 1_{v<T} + ∫ₜᵛ Γ_s δ_s ds | 𝓕_t]`. -/
theorem affine_representation {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : Peng1990.SMP.IsStdBrownian P B)
    (T : ℝ≥0) (ξ : Ω → ℝ) (S : ℝ≥0 → Ω → ℝ)
    (δ β : ℝ≥0 → Ω → ℝ) (γ : ℝ≥0 → Ω → Fin d → ℝ)
    (hδ : Peng1990.SMP.L2F (augFiltration hB) P T δ)
    (hβ : IsStronglyProgressive (augFiltration hB) β)
    (hγ : IsStronglyProgressive (augFiltration hB) γ)
    (hC : ∃ C : ℝ, ∀ᵐ ω ∂P, ∀ t ≤ T, |β t ω| + eucNorm (γ t ω) ≤ C)
    (hdata : StandingData (augFiltration hB) P T ξ
      (fun t ω y z => δ t ω + β t ω * y + dot (γ t ω) z) S)
    (hS2 : InS2 (augFiltration hB) P T S)
    (J : Fin d → ℝ≥0 → Ω → ℝ) (hJ : IsContItoIntegral (augFiltration hB) P T B γ J)
    (Y : ℝ≥0 → Ω → ℝ) (Z : ℝ≥0 → Ω → Fin d → ℝ) (K : ℝ≥0 → Ω → ℝ)
    (hsol : IsRBSDESolution (augFiltration hB) P T B ξ
      (fun t ω y z => δ t ω + β t ω * y + dot (γ t ω) z) S Y Z K) :
    ∀ t ≤ T, IsEssSup P (augFiltration hB t)
      {X | ∃ v ∈ stoppingTimesFrom (augFiltration hB) T t,
        X = P[affinePayoff T ξ S δ β γ J t v | augFiltration hB t]}
      (fun ω => linGamma β γ J 0 t ω * Y t ω) := by sorry

end ReflectedBSDE.StoppingControl
