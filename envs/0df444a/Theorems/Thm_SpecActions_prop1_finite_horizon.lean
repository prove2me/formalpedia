-- Prove2me | Theorems.Thm_SpecActions_prop1_finite_horizon
-- name    : SpecActions.prop1_finite_horizon
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-10T18:42:41.328328+00:00
-- url     : https://prove2.me/theorems/04b50689-e0c2-45bc-8d9c-746726a398e9
-- title:
--   Proposition 1 — finite-horizon latency ratio (goal theorem)
-- statement:
--   Under Assumptions 1–2 of the paper, with per-step hit probability $p_k=p(k)$, speculator latency $\mathrm{Exp}(\alpha)$ and real-call latency $\mathrm{Exp}(\beta)$, the ratio of the expected runtime of Algorithm 1 to that of strictly sequential execution is
--
--   $$\frac{\mathbb{E}[T_{\mathrm{spec}}]}{\mathbb{E}[T_{\mathrm{seq}}]}=1-\frac{1}{T}\,\frac{\alpha}{\alpha+\beta}\left[\frac{(T-1)p_k}{1+p_k}+\frac{p_k^2}{(1+p_k)^2}-\frac{p_k^2}{(1+p_k)^2}(-p_k)^{T-1}\right]$$
--
--   for every horizon $T\ge 1$, $\alpha,\beta>0$ and $p_k\in[0,1]$.
--
--   Here $\mathbb{E}[T_{\mathrm{seq}}]=T/\beta$ and $\mathbb{E}[T_{\mathrm{spec}}]=T/\beta-S_{T-1}\cdot\frac{\alpha}{\beta(\alpha+\beta)}$, the sequential runtime less one expected saving per hit. The identity is the goal theorem of this mission.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, Proposition 1 (p. 4), with proof in Appendix A (pp. 13–14)

import Definitions.Def_SpecActions_model

import Definitions.Def_SpecActions_model

namespace SpecActions
theorem prop1_finite_horizon (T : ℕ) (α β pk : ℝ) (hT : 1 ≤ T)
    (hα : 0 < α) (hβ : 0 < β) (hpk0 : 0 ≤ pk) (hpk1 : pk ≤ 1) :
    specTime T α β pk / seqTime T β
      = 1 - (1 / (T : ℝ)) * (α / (α + β)) *
          (((T : ℝ) - 1) * pk / (1 + pk)
            + pk ^ 2 / (1 + pk) ^ 2
            - pk ^ 2 / (1 + pk) ^ 2 * (-pk) ^ (T - 1)) := by sorry
end SpecActions
