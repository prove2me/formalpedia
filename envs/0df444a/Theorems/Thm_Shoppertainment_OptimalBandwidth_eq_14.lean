-- Prove2me | Theorems.Thm_Shoppertainment_OptimalBandwidth_eq_14
-- name    : Shoppertainment.OptimalBandwidth.eq_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:49:58.487813+00:00
-- url     : https://prove2.me/theorems/5dfafaa5-e9b3-4538-a44f-d31906c5a109
-- title:
--   (14), p. 31 — individual profitability π(te) = α(∫_{q̲}^{q̂} pL dF + ∫_{q̂}^1 pH q dF) for te > t̂e, else α∫_{q̲}^1 pH q dF
-- statement:
--   Let $0 < \alpha < 1$, $v > 0$ and $0 \le \underline q < 1$, with qualities uniform on $[\underline q, 1]$ ($dF(q) = dq/(1-\underline q)$). Let $\pi(t_e)$ be the streamer's expected commission from one attending consumer when every manufacturer prices according to Lemma 2: under low pricing the consumer always buys at $p_L$, under high pricing only after a good signal (probability $q$) at $p_H$. Then for every $t_e \in [0,1]$,
--   $$\pi(t_e) = \begin{cases} \alpha\left(\displaystyle\int_{\underline q}^{\hat q} p_L\,dF(q) + \int_{\hat q}^{1} p_H\,q\,dF(q)\right) & \text{if } t_e > \hat t_e,\\[3mm] \alpha\displaystyle\int_{\underline q}^{1} p_H\,q\,dF(q) & \text{if } t_e \le \hat t_e,\end{cases}$$
--   with $p_H = (1 - t_e + t_e q)v$, $p_L = t_e q v$, $\hat t_e = 1/(2-\underline q)$ and $\hat q = 2 - 1/t_e$.
--
--   This is the per-consumer half of the streamer's payoff $\Pi = T\cdot\pi$.
--
--   **Formalization Note** $\pi$ is defined as $\alpha$ times the average, over the uniform law, of $p\cdot D(p)/T$ at each manufacturer's equilibrium price $p$, with $D$ the demand (8); the display (14) is therefore a theorem about that definition. $\underline q < 1$ is pinned for the uniform law.
-- source:
--   Gu, Zhao & Wu, A Model of Shoppertainment Live Streaming, accepted manuscript (Management Science, forthcoming, Oct. 2024), p. 31, display (14)

import Mathlib
import Definitions.Def_Shoppertainment_OptimalBandwidth_Model

namespace Shoppertainment.OptimalBandwidth

theorem eq_14 (α v ql : ℝ) (hα : 0 < α) (hα1 : α < 1) (hv : 0 < v) (hql : 0 ≤ ql) (hql1 : ql < 1) :
    ∀ te ∈ Set.Icc (0:ℝ) 1, profitability α v ql te =
      if teHat ql < te then
        α * ((1 / (1 - ql)) * (∫ q in ql..qHat te, pL v te q) +
          (1 / (1 - ql)) * ∫ q in qHat te..1, pH v te q * q)
      else α * ((1 / (1 - ql)) * ∫ q in ql..1, pH v te q * q) := by sorry

end Shoppertainment.OptimalBandwidth
