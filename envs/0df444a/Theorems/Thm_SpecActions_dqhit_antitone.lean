-- Prove2me | Theorems.Thm_SpecActions_dqhit_antitone
-- name    : SpecActions.dqhit_antitone
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-10T18:58:37.318833+00:00
-- url     : https://prove2.me/theorems/e9e212e2-02a3-4bc1-b3b8-ef655e517104
-- title:
--   Diminishing marginal returns of speculative breadth
-- statement:
--   At a speculation window let $p^{(1)}\ge p^{(2)}\ge\cdots$ be the realized per-branch confidences, and let
--
--   $$q(m)=1-\prod_{j<m}\bigl(1-p^{(j)}\bigr)$$
--
--   be the probability of obtaining a cached action when the top $m$ branches are launched. The marginal gain from adding one more branch,
--
--   $$\delta q(m)=q(m+1)-q(m)=\Bigl(\prod_{j<m}(1-p^{(j)})\Bigr)p^{(m)},$$
--
--   is non-increasing in $m$ whenever the confidences lie in $[0,1]$ and are sorted in descending order. Both factors are non-increasing in $m$, which is what makes the optimal breadth a threshold rule.
-- source:
--   Ye, Ahuja, Liargkovas, Lu, Kaffes, Peng, "Speculative Actions: A Lossless Framework for Faster Agentic Systems", ICLR 2026, arXiv:2510.04371, https://arxiv.org/abs/2510.04371, Corollary 5 proof, Appendix C.3 (pp. 22–23): "$\delta q(m;p)$ is nonincreasing in $m$ (diminishing returns)"

import Definitions.Def_SpecActions_model

import Definitions.Def_SpecActions_model

namespace SpecActions
theorem dqhit_antitone (pv : ℕ → ℝ) (hpv0 : ∀ j, 0 ≤ pv j) (hpv1 : ∀ j, pv j ≤ 1)
    (hsorted : ∀ i j, i ≤ j → pv j ≤ pv i) (m : ℕ) :
    dqhit pv (m + 1) ≤ dqhit pv m := by sorry
end SpecActions
