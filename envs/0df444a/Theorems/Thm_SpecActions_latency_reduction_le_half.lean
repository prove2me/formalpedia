-- Prove2me | Theorems.Thm_SpecActions_latency_reduction_le_half
-- name    : SpecActions.latency_reduction_le_half
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-10T18:43:10.748717+00:00
-- url     : https://prove2.me/theorems/0cd334d1-8e11-4a64-89e1-71c0805f69ae
-- title:
--   The 50% latency-reduction ceiling for breadth speculation
-- statement:
--   For all $\alpha,\beta>0$ and $p_k\in[0,1]$ the asymptotic latency reduction achieved by single-step breadth speculation is strictly less than one half:
--
--   $$\frac{p_k}{1+p_k}\cdot\frac{\alpha}{\alpha+\beta}<\frac12 .$$
--
--   This is the negative result motivating the depth-focused regime: the paper's "upper bound of 50%, occurring when $p=1$ and $\alpha=\infty$" describes a supremum that is approached but never attained, since $\frac{p_k}{1+p_k}\le\frac12$ with equality only at $p_k=1$, while $\frac{\alpha}{\alpha+\beta}<1$ for every finite $\alpha$ and $\beta>0$.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, Proposition 1 discussion (p. 5): "the end-to-end latency reduction has an upper bound of 50%"

import Definitions.Def_SpecActions_model

import Definitions.Def_SpecActions_model

namespace SpecActions
theorem latency_reduction_le_half (α β pk : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hpk0 : 0 ≤ pk) (hpk1 : pk ≤ 1) :
    pk / (1 + pk) * (α / (α + β)) < 1 / 2 := by sorry
end SpecActions
