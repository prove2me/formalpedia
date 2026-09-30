-- Prove2me | Theorems.Thm_SpecActions_phit_bounds
-- name    : SpecActions.phit_bounds
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-10T18:42:04.388693+00:00
-- url     : https://prove2.me/theorems/79200a82-1ec6-45e4-bdb0-593819d18252
-- title:
--   Range and monotonicity of the $k$-branch hit probability $p(k)$
-- statement:
--   For a per-branch success probability $p\in[0,1]$ and any breadth $k$, the probability that at least one of $k$ independent speculative branches implies the correct next call, $p(k)=1-(1-p)^k$, lies in $[0,1]$ and is non-decreasing in $k$.
--
--   These are the range facts that the latency and cost theorems assume of their $p_k$ argument, together with the statement that widening speculation never lowers the per-step hit probability.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, §5.1 / Appendix C.1 (p. 19), definition of $p(k)=1-(1-p)^k$

import Definitions.Def_SpecActions_model

import Definitions.Def_SpecActions_model

namespace SpecActions
theorem phit_bounds (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ phit k p ∧ phit k p ≤ 1 ∧ phit k p ≤ phit (k + 1) p := by sorry
end SpecActions
