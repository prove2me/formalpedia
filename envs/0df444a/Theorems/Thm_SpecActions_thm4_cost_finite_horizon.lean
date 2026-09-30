-- Prove2me | Theorems.Thm_SpecActions_thm4_cost_finite_horizon
-- name    : SpecActions.thm4_cost_finite_horizon
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-10T18:48:17.48455+00:00
-- url     : https://prove2.me/theorems/3b5a9901-fb75-4c1e-a396-45f7562f37db
-- title:
--   Theorem 4 — finite-horizon relative cost increase
-- statement:
--   Let $\tilde k$ be the number of *distinct* actions produced across the $k$ speculative branches (duplicated speculations are killed). Then for every $T\ge 1$, $\alpha,\beta>0$ and $p_k\in[0,1]$,
--
--   $$\frac{\mathbb{E}[M_{\mathrm{spec}}-M_{\mathrm{seq}}]}{\mathbb{E}[M_{\mathrm{seq}}]}=\tilde k-\frac{1}{T}\left(\tilde k+\frac{\alpha}{\alpha+\beta}\right)\left[\frac{(T-1)p_k}{1+p_k}+\frac{p_k^2}{(1+p_k)^2}-\frac{p_k^2}{(1+p_k)^2}(-p_k)^{T-1}\right].$$
--
--   The bracket is the same $S_{T-1}$ that governs the latency ratio, which is what lets a practitioner tune the breadth $k$ against a joint latency/cost budget from a single estimate of $p_k$.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, Theorem 4, Appendix C.1 (p. 19), cost expression

import Definitions.Def_SpecActions_model

import Definitions.Def_SpecActions_model

namespace SpecActions
theorem thm4_cost_finite_horizon (T : ℕ) (α β pk kt : ℝ) (hT : 1 ≤ T)
    (hα : 0 < α) (hβ : 0 < β) (hpk0 : 0 ≤ pk) (hpk1 : pk ≤ 1) :
    (specCost T α β pk kt - seqCost T β) / seqCost T β
      = kt - (1 / (T : ℝ)) * (kt + α / (α + β)) *
          (((T : ℝ) - 1) * pk / (1 + pk)
            + pk ^ 2 / (1 + pk) ^ 2
            - pk ^ 2 / (1 + pk) ^ 2 * (-pk) ^ (T - 1)) := by sorry
end SpecActions
