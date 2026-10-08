-- Prove2me | Theorems.Thm_SolomonRWRE_SlowApproach_lemma_2_7
-- name    : SolomonRWRE.SlowApproach.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:49.738769+00:00
-- url     : https://prove2.me/theorems/09837168-f49a-4b8e-8134-9e9584ed8162
-- title:
--   Lemma (2.7) — transform limits in the critical and supercritical regimes
-- statement:
--   For $u>0$, let $\varphi$ be the mirror-to-mirror transform and put $\nu=2\theta/(\theta-1)^2$, $K=(1-\gamma)\nu/\gamma$, $\omega(y)=\log_{1/\gamma}y$, and $\rho=\log_{1/\gamma}\theta>1$.
--
--   If $\gamma\theta=1$, then
--   $$
--   \lim_{y\to\infty}y\left(1-\varphi\left(\frac{u}{y\ln y}\right)\right)=\frac{2\theta}{(\theta-1)\ln\theta}u.
--   $$
--   If $\gamma\theta>1$, then the difference between $y(1-\varphi(u/y^\rho))$ and $Ku\sum_{j\in\mathbb Z}(\gamma\theta)^{j-\{\omega(y)\}}/(1+\nu u\theta^{j-\{\omega(y)\}})$ tends to zero.
--
--   These are the transform limits used to obtain the two different passage-time regimes.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 13, Lemma (2.7), displays (2.8)–(2.9)

import Mathlib
import Definitions.Def_SolomonRWRE_SlowApproach_Transforms
open Filter
open scoped Topology

namespace SolomonRWRE.SlowApproach

/-- Solomon, Lemma (2.7), p. 13, (2.8) and (2.9). The two regimes for the
small-argument transform. Formalization Note: the limits run through real `y` to infinity.
The paper's `φ` is written as `phiSeries`, which equals it by Lemma (2.5). -/
theorem lemma_2_7 (γ θ : ℝ) (hθ : 1 < θ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hcritical : 1 ≤ γ * θ) (u : ℝ) (hu : 0 < u) :
    (γ * θ = 1 →
      Filter.Tendsto
        (fun y : ℝ => y * (1 - phiSeries γ θ (u / (y * Real.log y))))
        Filter.atTop (𝓝 ((2 * θ / ((θ - 1) * Real.log θ)) * u))) ∧
    (1 < γ * θ →
      Filter.Tendsto
        (fun y : ℝ => y * (1 - phiSeries γ θ (u / y ^ (rho γ θ))) -
          K γ θ * u * laplaceSeries γ θ (Int.fract (Real.logb (1 / γ) y)) u)
        Filter.atTop (𝓝 0)) := by sorry

end SolomonRWRE.SlowApproach
