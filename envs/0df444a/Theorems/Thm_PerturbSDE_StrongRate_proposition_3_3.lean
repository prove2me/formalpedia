-- Prove2me | Theorems.Thm_PerturbSDE_StrongRate_proposition_3_3
-- name    : PerturbSDE.StrongRate.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:09:45.454877+00:00
-- url     : https://prove2.me/theorems/7ba75152-07c5-4cc8-b2f6-f915963f96cd
-- title:
--   Proposition 3.3, p. 19 — stopped-tamed Euler: sup_t ‖X_t − Y^θ_t‖_{L^r} ≤ C·mesh(θ)^{1/2} for all partitions θ
-- statement:
--   Let $d,m\in\mathbb N$, $r,\varepsilon,c,T\in(0,\infty)$, $q_0,q_1\in(0,\infty]$, $\alpha\in[0,\infty)$, $p\in[2,\infty)$ with $\frac1p+\frac1{q_0}+\frac1{q_1}=\frac1r$. Let $U_0\in\mathcal C^3_{\mathcal D}(\mathbb R^d,[0,\infty))$, $U_1\in\mathcal C^1_{\mathcal P}(\mathbb R^d,[0,\infty))$, $\mu\in\mathcal C^1_{\mathcal P}(\mathbb R^d,\mathbb R^d)$, $\sigma\in\mathcal C^1_{\mathcal P}(\mathbb R^d,\mathbb R^{d\times m})$ satisfy $\|x\|^{1/c}\le c(1+U_0(x))$ and, for all $x,y\in\mathbb R^d$,
--   $$(\mathcal G_{\mu,\sigma}U_0)(x)+\tfrac12\|\sigma(x)^*(\nabla U_0)(x)\|^2+U_1(x)\le\alpha U_0(x)+c,$$
--   $$\langle x-y,\mu(x)-\mu(y)\rangle+\tfrac{(p-1)(1+\varepsilon)}2\|\sigma(x)-\sigma(y)\|^2_{HS}\le\Big[c+\frac{U_0(x)+U_0(y)}{2q_0Te^{\alpha T}}+\frac{U_1(x)+U_1(y)}{2q_1e^{\alpha T}}\Big]\|x-y\|^2 .$$
--   Let $W$ be a standard $m$-dimensional $(\mathcal F_t)$-Brownian motion on a stochastic basis, $X$ an adapted continuous solution of $dX=\mu(X)dt+\sigma(X)dW$ on $[0,T]$ with $\mathbb E[e^{U_0(X_0)}]<\infty$, and, for every partition $\theta\in\mathcal P_T$, $Y^\theta$ an adapted process with continuous sample paths, $Y^\theta_0=X_0$, satisfying the stopped-tamed Euler–Maruyama recursion (76). Then there is $C\in[0,\infty)$ such that for every $\theta=(t_0,\dots,t_n)\in\mathcal P_T$,
--   $$\sup_{t\in[0,T]}\|X_t-Y^\theta_t\|_{L^r(\Omega;\mathbb R^d)}\le C\Big[\max_{0\le k\le n-1}|t_{k+1}-t_k|\Big]^{1/2}.$$
--
--   This is the continuous-time, all-partitions form of the strong rate $\frac12$ for the stopped-tamed scheme under non-globally monotone coefficients; Theorem 1.3 is its specialisation to uniform grids.
--
--   **Formalization Note** $C$ is chosen before $\theta$ and does not depend on it. The classes $\mathcal C^1_{\mathcal P}$ and $\mathcal C^3_{\mathcal D}$ are (13) and (12) (not $C^1$/$C^3$); on $\mathbb R^{d\times m}$ the Hilbert–Schmidt distance is used. $\frac{U_0(x)+U_0(y)}{2q_0Te^{\alpha T}}$ is written $q_0^{-1}(U_0(x)+U_0(y))/(2Te^{\alpha T})$, which is $0$ when $q_0=\infty$. The exponential moment is a Lebesgue integral in $[0,\infty]$; the $L^r$ norms and the supremum are in $[0,\infty]$. $X$ is the published `IsSolution` (normal filtration = right-continuity + completion; $W$ on $[0,\infty)$); each $Y^\theta$ is also assumed measurable, which (76) already forces on $[0,T]$.
-- source:
--   Hutzenthaler, Jentzen, arXiv:1401.0295v1, p. 19, Proposition 3.3, (76), (77)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_completedSDEPast
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_PerturbSDE_StrongRate_Setting
import Definitions.Def_PerturbSDE_StrongRate_Scheme

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PerturbSDE.StrongRate

open EthierKurtz SabanisEuler.Shared

/-- Hutzenthaler–Jentzen, arXiv:1401.0295v1, p. 19, Proposition 3.3, (77): under the
Lyapunov-type condition on `U_0 ∈ 𝒞³_𝒟(ℝ^d, [0, ∞))`, `U_1 ∈ 𝒞¹_𝒫(ℝ^d, [0, ∞))` and the
non-global monotonicity condition on `µ, σ ∈ 𝒞¹_𝒫`, there is `C ∈ [0, ∞)` such that for every
partition `θ ∈ 𝒫_T` the stopped-tamed Euler–Maruyama interpolation `Y^θ` of (76) satisfies
`sup_{t ∈ [0, T]} ‖X_t − Y^θ_t‖_{L^r} ≤ C (mesh θ)^{1/2}`. -/
theorem proposition_3_3 {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) {Ω : Type*}
    [mΩ : MeasurableSpace Ω]
    (r ε c : ℝ) (hr : 0 < r) (hε : 0 < ε) (hc : 0 < c) (T : ℝ≥0) (hT : 0 < T)
    (q₀ q₁ : ℝ≥0∞) (hq₀ : q₀ ≠ 0) (hq₁ : q₁ ≠ 0) (α : ℝ) (hα : 0 ≤ α) (p : ℝ) (hp : 2 ≤ p)
    (U₀ U₁ : SDEState d → ℝ) (mu : SDEState d → SDEState d)
    (sigma : SDEState d → Diffusion d m)
    (hU₀ : IsC3D U₀) (hU₀nn : ∀ x, 0 ≤ U₀ x) (hU₁ : IsPolyLocLip U₁) (hU₁nn : ∀ x, 0 ≤ U₁ x)
    (hmu : IsPolyLocLip mu) (hsigma : IsPolyLocLip sigma)
    (hexp : (ENNReal.ofReal p)⁻¹ + q₀⁻¹ + q₁⁻¹ = (ENNReal.ofReal r)⁻¹)
    (hgrowth : ∀ x : SDEState d, ‖x‖ ^ (1 / c) ≤ c * (1 + U₀ x))
    (hLyap : ∀ x : SDEState d,
      generator mu sigma U₀ x + 1 / 2 * noiseSq sigma U₀ x + U₁ x ≤ α * U₀ x + c)
    (hmono : ∀ x y : SDEState d,
      inner ℝ (x - y) (mu x - mu y) + (p - 1) * (1 + ε) / 2 * ‖sigma x - sigma y‖ ^ 2 ≤
        (c + (q₀⁻¹).toReal * (U₀ x + U₀ y) / (2 * T * Real.exp (α * T)) +
          (q₁⁻¹).toReal * (U₁ x + U₁ y) / (2 * Real.exp (α * T))) * ‖x - y‖ ^ 2)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (W : ℝ≥0 → Ω → SDEState m) (hW : IsWienerMartingale P ℱ W)
    (X : ℝ≥0 → Ω → SDEState d) (Y : Partition T → ℝ≥0 → Ω → SDEState d)
    (hX : IsSolution P ℱ W T (X 0) (fun z => mu z.2) (fun z => sigma z.2) X)
    (hYm : ∀ θ t, Measurable (Y θ t))
    (hYa : ∀ θ t, Measurable[completedSDEPast P ℱ t] (Y θ t))
    (hYc : ∀ θ ω, ContinuousOn (fun t => Y θ t ω) (Set.Icc 0 T))
    (hEexp : ∫⁻ ω, ENNReal.ofReal (Real.exp (U₀ (X 0 ω))) ∂P < ⊤)
    (hY0 : ∀ θ ω, Y θ 0 ω = X 0 ω)
    (hY : ∀ θ, IsStoppedTamedScheme mu sigma W θ (Y θ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : Partition T,
      ⨆ t ∈ Set.Icc (0 : ℝ≥0) T, eLpNorm (fun ω => X t ω - Y θ t ω) (ENNReal.ofReal r) P ≤
        ENNReal.ofReal (C * Real.sqrt θ.mesh) := by sorry

end PerturbSDE.StrongRate
