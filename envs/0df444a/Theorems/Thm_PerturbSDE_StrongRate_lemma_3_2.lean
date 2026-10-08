-- Prove2me | Theorems.Thm_PerturbSDE_StrongRate_lemma_3_2
-- name    : PerturbSDE.StrongRate.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:09:39.190691+00:00
-- url     : https://prove2.me/theorems/0577f884-eb3d-4d1a-9f23-2fd8920b9098
-- title:
--   Lemma 3.2, pp. 16–17 — one-partition error estimate (64) for the scheme (63) stopped at the first grid exit from 𝒪
-- statement:
--   Let $d,m,n\in\mathbb N$, $0=t_0<t_1<\dots<t_n=T<\infty$, let $\mathcal O\subseteq\mathbb R^d$ be Borel, and let $\phi:\mathbb R^d\to\mathbb R$, $\mu:\mathbb R^d\to\mathbb R^d$, $\sigma:\mathbb R^d\to\mathbb R^{d\times m}$ be measurable with
--   $$\|\mu(x)-\mu(y)\|\vee\|\sigma(x)-\sigma(y)\|_{HS}\le(\phi(x)+\phi(y))\|x-y\|\qquad\text{for all }x,y.$$
--   Let $W$ be a standard $(\mathcal F_t)$-Brownian motion on a stochastic basis, let $X$ be an adapted continuous solution of $dX=\mu(X)dt+\sigma(X)dW$, and let $Y$ be adapted with continuous sample paths, $Y_0=X_0$, satisfying (63): $Y_t=Y_{t_k}+\mathbb 1_{\{Y_{t_k}\in\mathcal O\}}\psi\big(\mu(Y_{t_k})(t-t_k)+\sigma(Y_{t_k})(W_t-W_{t_k})\big)$ for $t\in[t_k,t_{k+1}]$, with $\psi(v)=v/(1+\|v\|^2)$. Let $\tau=\inf(\{T\}\cup\{t\in\{t_0,\dots,t_n\}:Y_t\notin\mathcal O\})$. Then for all stopping times $\nu:\Omega\to[0,T]$, all $\varepsilon,r\in(0,\infty)$, $p\in[2,\infty)$ and $q,u,v\in(0,\infty]$ with $\frac1p+\frac1q=\frac1r$ and $\frac1u+\frac1v=\frac1p$,
--   $$\begin{aligned}\|X_{\nu\wedge\tau}-Y_{\nu\wedge\tau}\|_{L^r(\Omega)}\le{}&\sup_{s\in[0,T]}\max\big(1,\sqrt T\|\mu(Y_s)\|_{L^v(\Omega)}+v\|\sigma(Y_s)\|_{L^v(\Omega;HS)}\big)\cdot30\,p\,(1+\tfrac1\varepsilon)\,e^T\\&\cdot\Big\|\exp\Big(\int_0^{\nu\wedge\tau}\big[R_{p,\varepsilon}(X_s,Y_s)\big]^+ds\Big)\Big\|_{L^q(\Omega)}\\&\cdot\Big[\sup_{s\in[0,T]}\big\|\|\mu(Y_s)\|+[1\vee\|\sigma(Y_s)\|_{HS}]^2+|\phi(Y_s)|\big\|_{L^u(\Omega)}\Big]\Big[\max_{0\le k\le n-1}|t_{k+1}-t_k|\Big]^{1/2},\end{aligned}$$
--   where $R_{p,\varepsilon}(x,y)=\big(\langle x-y,\mu(x)-\mu(y)\rangle+\frac{(p-1)(1+\varepsilon)}2\|\sigma(x)-\sigma(y)\|^2_{HS}\big)/\|x-y\|^2$ (with $0/0=0$).
--
--   This is the one-partition error bound for tamed-and-stopped Euler-type schemes; Proposition 3.3 shows that its right-hand side is finite and of order $|\theta|^{1/2}$ for the stopped-tamed scheme.
--
--   **Formalization Note** The page reads "$\int_0^T\|\mu(X_s)\|+\|\sigma(X_s)\|^2ds$ $\mathbb P$-a.s." without "$<\infty$"; it is read as "$<\infty$ $\mathbb P$-a.s.", which the published `IsSolution` provides. The factor $v$ in front of $\|\sigma(Y_s)\|_{L^v}$ is a number in $(0,\infty]$; the whole right-hand side lies in $[0,\infty]$ with $0\cdot\infty=0$. Stopping times $\nu$ range over all stopping times of the $\mathbb P$-completed filtration. Normal filtration = right-continuity + completion; $W$ lives on $[0,\infty)$; (63) is required for every $\omega$; $Y$ is also assumed measurable, which (63) already forces on $[0,T]$.
-- source:
--   Hutzenthaler, Jentzen, arXiv:1401.0295v1, pp. 16–17, Lemma 3.2, (63), (64)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_completedSDEPast
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_PerturbSDE_StrongRate_Setting
import Definitions.Def_PerturbSDE_StrongRate_Perturbation
import Definitions.Def_PerturbSDE_StrongRate_Scheme

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PerturbSDE.StrongRate

open EthierKurtz SabanisEuler.Shared

/-- Hutzenthaler–Jentzen, arXiv:1401.0295v1, pp. 16–17, Lemma 3.2, (64): one-partition error
estimate for the scheme (63) with indicator `𝟙_{Y_{t_k} ∈ O}`, stopped at
`τ = inf({T} ∪ {t ∈ {t_0, …, t_n} : Y_t ∉ O})`. For every stopping time `ν ≤ T`, all
`ε, r ∈ (0, ∞)`, `p ∈ [2, ∞)`, `q, u, v ∈ (0, ∞]` with `1/p + 1/q = 1/r`, `1/u + 1/v = 1/p`:
`‖X_{ν∧τ} − Y_{ν∧τ}‖_{L^r} ≤ sup_s max(1, √T ‖µ(Y_s)‖_{L^v} + v ‖σ(Y_s)‖_{L^v})
 · 30 p (1 + 1/ε) e^T ‖exp(∫_0^{ν∧τ} [monotonicity ratio]^+ ds)‖_{L^q}
 · [sup_s ‖ ‖µ(Y_s)‖ + [1 ∨ ‖σ(Y_s)‖]² + |φ(Y_s)| ‖_{L^u}] (mesh θ)^{1/2}`,
all in `[0, ∞]`. -/
theorem lemma_3_2 {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (T : ℝ≥0) (θ : Partition T) (O : Set (SDEState d)) (hO : MeasurableSet O)
    (φ : SDEState d → ℝ) (mu : SDEState d → SDEState d) (sigma : SDEState d → Diffusion d m)
    (hφ : Measurable φ) (hmu : Measurable mu) (hsigma : Measurable sigma)
    (hLip : ∀ x y : SDEState d,
      max ‖mu x - mu y‖ ‖sigma x - sigma y‖ ≤ (φ x + φ y) * ‖x - y‖)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (W : ℝ≥0 → Ω → SDEState m) (hW : IsWienerMartingale P ℱ W)
    (X Y : ℝ≥0 → Ω → SDEState d)
    (hX : IsSolution P ℱ W T (X 0) (fun z => mu z.2) (fun z => sigma z.2) X)
    (hYm : ∀ t, Measurable (Y t)) (hYa : ∀ t, Measurable[completedSDEPast P ℱ t] (Y t))
    (hYc : ∀ ω, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T))
    (hY0 : ∀ ω, Y 0 ω = X 0 ω)
    (hY : IsIndicatorTamedScheme mu sigma W θ O Y) :
    ∀ ν : Ω → ℝ≥0, IsStopTime P ℱ T ν →
    ∀ ε r : ℝ, 0 < ε → 0 < r → ∀ p : ℝ, 2 ≤ p →
    ∀ q u v : ℝ≥0∞, q ≠ 0 → u ≠ 0 → v ≠ 0 →
      (ENNReal.ofReal p)⁻¹ + q⁻¹ = (ENNReal.ofReal r)⁻¹ →
      u⁻¹ + v⁻¹ = (ENNReal.ofReal p)⁻¹ →
      eLpNorm (fun ω => X (min (ν ω) (exitTime θ O Y ω)) ω -
          Y (min (ν ω) (exitTime θ O Y ω)) ω) (ENNReal.ofReal r) P ≤
        (⨆ s ∈ Set.Icc (0 : ℝ≥0) T,
            max 1 (ENNReal.ofReal (Real.sqrt T) * eLpNorm (fun ω => mu (Y s ω)) v P +
              v * eLpNorm (fun ω => sigma (Y s ω)) v P)) *
          ENNReal.ofReal (30 * p * (1 + 1 / ε) * Real.exp T) *
          eLpNorm (expPosIntegral
              (fun s ω => monoRatio mu sigma p (ENNReal.ofReal ε) (X s ω) (Y s ω))
              (fun ω => min (ν ω) (exitTime θ O Y ω))) q P *
          (⨆ s ∈ Set.Icc (0 : ℝ≥0) T,
            eLpNorm (fun ω => ‖mu (Y s ω)‖ + (max 1 ‖sigma (Y s ω)‖) ^ 2 + |φ (Y s ω)|) u P) *
          ENNReal.ofReal (Real.sqrt θ.mesh) := by sorry

end PerturbSDE.StrongRate
