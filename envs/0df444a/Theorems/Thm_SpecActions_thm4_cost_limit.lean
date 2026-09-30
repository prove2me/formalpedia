-- Prove2me | Theorems.Thm_SpecActions_thm4_cost_limit
-- name    : SpecActions.thm4_cost_limit
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-10T18:53:28.498201+00:00
-- url     : https://prove2.me/theorems/61564c7c-2b82-4e38-9569-537e1a0a56cd
-- title:
--   Theorem 4 — asymptotic relative cost increase
-- statement:
--   As the horizon grows, the relative cost increase of Algorithm 1 converges:
--
--   $$\frac{\mathbb{E}[M_{\mathrm{spec}}-M_{\mathrm{seq}}]}{\mathbb{E}[M_{\mathrm{seq}}]}\;\xrightarrow[T\to\infty]{}\;\tilde k-\left(\tilde k+\frac{\alpha}{\alpha+\beta}\right)\frac{p_k}{1+p_k}$$
--
--   for all $\alpha,\beta>0$ and $p_k\in[0,1]$, with $\tilde k$ the number of distinct actions across the $k$ branches. Paired with the asymptotic latency ratio, this is the closed-form Pareto trade-off the paper uses to choose the speculative breadth offline.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, Theorem 4, Appendix C.1 (p. 19), the $T\to\infty$ limit; also §5.1 (p. 9)

import Definitions.Def_SpecActions_model

import Definitions.Def_SpecActions_model
import Mathlib.Order.Filter.AtTopBot.Basic

namespace SpecActions
open Filter Topology
theorem thm4_cost_limit (α β pk kt : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hpk0 : 0 ≤ pk) (hpk1 : pk ≤ 1) :
    Tendsto (fun T : ℕ => (specCost T α β pk kt - seqCost T β) / seqCost T β)
      atTop (𝓝 (kt - (kt + α / (α + β)) * (pk / (1 + pk)))) := by sorry
end SpecActions
