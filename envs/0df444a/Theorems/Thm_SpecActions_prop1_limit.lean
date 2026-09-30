-- Prove2me | Theorems.Thm_SpecActions_prop1_limit
-- name    : SpecActions.prop1_limit
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-10T18:42:55.577422+00:00
-- url     : https://prove2.me/theorems/44875867-c0b3-4957-8cc7-87b08168ed6b
-- title:
--   Proposition 1 — asymptotic latency ratio as $T\to\infty$
-- statement:
--   As the horizon grows, the latency ratio of Algorithm 1 converges:
--
--   $$\frac{\mathbb{E}[T_{\mathrm{spec}}]}{\mathbb{E}[T_{\mathrm{seq}}]}\;\xrightarrow[T\to\infty]{}\;1-\frac{p_k}{1+p_k}\cdot\frac{\alpha}{\alpha+\beta}$$
--
--   for all $\alpha,\beta>0$ and $p_k\in[0,1]$. The oscillating term $(-p_k)^{T-1}$ is bounded but does not vanish termwise in an obvious way, so it must be controlled uniformly before the $1/T$ prefactor is taken to zero.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, Proposition 1 (p. 4), the $T\to\infty$ limit; Appendix A (p. 14)

import Definitions.Def_SpecActions_model

import Definitions.Def_SpecActions_model
import Mathlib.Order.Filter.AtTopBot.Basic

namespace SpecActions
open Filter Topology
theorem prop1_limit (α β pk : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hpk0 : 0 ≤ pk) (hpk1 : pk ≤ 1) :
    Tendsto (fun T : ℕ => specTime T α β pk / seqTime T β) atTop
      (𝓝 (1 - pk / (1 + pk) * (α / (α + β)))) := by sorry
end SpecActions
