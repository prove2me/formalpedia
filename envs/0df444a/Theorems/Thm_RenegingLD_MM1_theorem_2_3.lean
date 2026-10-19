-- Prove2me | Theorems.Thm_RenegingLD_MM1_theorem_2_3
-- name    : RenegingLD.MM1.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:43.12119+00:00
-- url     : https://prove2.me/theorems/2c6411ce-55e2-42e8-829f-0939c4d73ed0
-- title:
--   Theorem 2.3, p. 7 — for λ ≥ µ, I*_{γ,T}/T, I_{γ,T}/T and Ĩ_{γ,T}/T converge to C(γ), which does not depend on the reneging rate θ
-- statement:
--   Consider the single-server queue with Poisson arrivals at rate $\lambda$, exponential service at rate $\mu$ and exponential reneging at rate $\theta$ per waiting customer, started from scaled queue length $x_0\ge0$, and let $I_T$ be the rate function (2.6) of the large deviation principle for (queue length, cumulative reneging) on $[0,T]$. With
--   $$I^*_{\gamma,T}=\inf\{I_T(\xi,\zeta):\zeta(T)=\gamma T\},\quad I_{\gamma,T}=\inf\{I_T(\xi,\zeta):\zeta(T)\ge\gamma T\},\quad \tilde I_{\gamma,T}=\inf\{I_T(\xi,\zeta):\zeta(T)\le\gamma T\},$$
--   $z_\gamma=(\sqrt{\gamma^2+4\lambda\mu}-\gamma)/(2\mu)$ and $C(\gamma)=\lambda(1-z_\gamma^{-1})+\mu(1-z_\gamma)-\gamma\log z_\gamma$: suppose $\lambda\ge\mu$. Then
--   $$\lim_{T\to\infty}\frac{I^*_{\gamma,T}}{T}=C(\gamma)\ \ (\gamma\ge0),\qquad \lim_{T\to\infty}\frac{I_{\gamma,T}}{T}=C(\gamma)\ \ (\gamma\ge\lambda-\mu),\qquad \lim_{T\to\infty}\frac{\tilde I_{\gamma,T}}{T}=C(\gamma)\ \ (0\le\gamma\le\lambda-\mu).$$
--
--   The decay rate $C(\gamma)$ involves $\lambda$, $\mu$ and $\gamma$ only: the reneging rate $\theta$ enters $I_T$ but not the limit, and neither does $x_0$. This is the "reneging paradox": over long horizons the probability of observing reneging at an atypical rate $\gamma$ decays like $e^{-nTC(\gamma)}$ whatever the customers' patience.
--
--   **Formalization Note.** `lam`, `mu` stand for $\lambda,\mu$. The positivity of $\lambda,\mu,\theta$ and $x_0\ge0$ are the paper's standing assumptions (§2). The values $I^*,I,\tilde I$ lie in $[0,\infty]$, the ratio is $I/T$ in $[0,\infty]$, and the limit is $C(\gamma)$ embedded in $[0,\infty]$; since $C(\gamma)\ge0$ this is exactly the real limit, and it also forces $I/T$ to be finite for large $T$.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 7, Theorem 2.3, (2.8)–(2.10)

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem theorem_2_3 (lam mu θ : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hθ : 0 < θ) (hlm : mu ≤ lam) (x0 : ℝ) (hx0 : 0 ≤ x0) :
    (∀ γ : ℝ, 0 ≤ γ →
      Tendsto (fun T => Istar lam mu θ x0 γ T / ENNReal.ofReal T) atTop
        (𝓝 (ENNReal.ofReal (C lam mu γ)))) ∧
    (∀ γ : ℝ, lam - mu ≤ γ →
      Tendsto (fun T => Iup lam mu θ x0 γ T / ENNReal.ofReal T) atTop
        (𝓝 (ENNReal.ofReal (C lam mu γ)))) ∧
    (∀ γ : ℝ, 0 ≤ γ → γ ≤ lam - mu →
      Tendsto (fun T => Idown lam mu θ x0 γ T / ENNReal.ofReal T) atTop
        (𝓝 (ENNReal.ofReal (C lam mu γ)))) := by sorry

end RenegingLD.MM1
