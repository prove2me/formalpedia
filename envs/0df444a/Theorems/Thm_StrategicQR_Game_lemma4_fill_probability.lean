-- Prove2me | Theorems.Thm_StrategicQR_Game_lemma4_fill_probability
-- name    : StrategicQR.Game.lemma4_fill_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:25:31.469678+00:00
-- url     : https://prove2.me/theorems/93853723-fd75-4073-a213-c54929b3f5af
-- title:
--   Lemma 4 (i), p. 15 — the threshold consumer's probability of a sale-period unit: $F(D_l)$ without rationing
-- statement:
--   Let $0<\alpha\le1$, $q>0$ and $\hat v\in[\underline v,\bar v]$, and let $D_\theta=\theta q/(1-\xi+\theta\xi)$. The probability that the threshold consumer buys in the sale period and receives a unit is
--   $$\Pr(D<D_l\text{ and a unit is received})=\begin{cases}F(D_l) & \text{if } s_l\bar G(\hat v)\le\theta s_m\bar G(s_m),\\[4pt] F(D_\theta)+\displaystyle\int_{D_\theta}^{D_l}\frac{\theta I}{(1-\xi)x}\,dF(x) & \text{otherwise,}\end{cases}$$
--   with $I=q-\xi x$. For $\theta>0$ the case condition is equivalent to $D_l\le D_\theta$.
--
--   The lemma shows that when strategic consumers are optimistic enough, rationing in the sale period never binds when the deep discount is offered, so $\theta$ drops out of the consumer's problem.
--
--   **Formalization Note** The printed case condition is $\theta_c=s_l/s_m\le\theta$. That is equivalent to $D_l\le D_\theta$ only when $s_m=\hat v$, and the printed lemma is false otherwise. Counterexample: $\bar v=10$, $\underline v=2$, $v_B=1$, $v_M-p=1$, $\alpha=1$, $q=1$, $\theta=\theta_c=0.2$, $\hat v=3$ (so $s_m=5$, $D_l\approx0.308>D_\theta\approx0.222$), exponential demand with rate $2.3625$. There the probability is $0.5000$ and $\hat v=3$ is a best response to $q$, but $F(D_l)\approx0.517$. The corrected condition is used. The printed lemma's hypothesis that beliefs are correct is then unnecessary: the formula holds for every belief.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 15, Lemma 4 (i); Technical Appendix p. 4 (PDF 36), proof of Lemma 4

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

namespace StrategicQR.Game

/-- Lemma 4 (i) (p. 15; proof on Technical Appendix p. 4), with the case condition corrected.
For `0 < α ≤ 1`, `q > 0` and any belief `v̂ ∈ [v̲, v̄]`, the probability that the threshold
consumer buys and receives a unit in the sale period is `F(D_l)` when
`s_l Ḡ(v̂) ≤ θ s_m Ḡ(s_m)`, and `F(D_θ) + ∫_{D_θ}^{D_l} θ I / ((1 - ξ) x) dF(x)`,
`I = q - ξ x`, otherwise; for `θ > 0` the case condition is equivalent to `D_l ≤ D_θ`. -/
theorem lemma4_fill_probability (M : Model) {α q vhat : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hq : 0 < q) (hv : vhat ∈ Set.Icc M.vlo M.vhi) :
    (0 < M.θ → (M.vB * Gbar M vhat ≤ M.θ * sm M vhat * Gbar M (sm M vhat) ↔
      Dl M α q vhat ≤ Dtheta M α q vhat)) ∧
    (M.vB * Gbar M vhat ≤ M.θ * sm M vhat * Gbar M (sm M vhat) →
      fillProb M α q vhat = demandCdf M.f (Dl M α q vhat)) ∧
    (M.θ * sm M vhat * Gbar M (sm M vhat) < M.vB * Gbar M vhat →
      fillProb M α q vhat = demandCdf M.f (Dtheta M α q vhat) +
        ∫ x in (Dtheta M α q vhat)..(Dl M α q vhat),
          M.θ * (q - xi M α vhat * x) / ((1 - xi M α vhat) * x) * M.f x) := by sorry

end StrategicQR.Game
