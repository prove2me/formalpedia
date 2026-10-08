-- Prove2me | Theorems.Thm_ResolvingNRM_IRT_tau_Kirt_le_exp_one
-- name    : ResolvingNRM.IRT.tau_Kirt_le_exp_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:21:24.504862+00:00
-- url     : https://prove2.me/theorems/98613fc6-b1cb-42c0-ae7a-62e2437c28bf
-- title:
--   p. 30 — with $K = \lceil \log\log T/\log(6/5)\rceil$, $T^{(5/6)^K} \le e$
-- statement:
--   Let $K(T) = \lceil \log\log T / \log(6/5) \rceil$ be the number of re-solves of the IRT policy. For every real $T \ge 1$,
--   $$T^{(5/6)^{K(T)}} \le e .$$
--
--   In words: the time remaining at the last re-solving time of IRT, $\tau_K = T^{(5/6)^K}$, is at most $e$, so the last epoch of IRT, where no thresholds are used, has bounded length.
--
--   **Formalization Note** For $1 \le T \le e$ the printed formula for $K$ is undefined ($T = 1$, $\log 0$) or negative; with Lean's conventions $\log 0 = 0$ and $\lceil y\rceil_{\mathbb N} = 0$ for $y \le 0$, $K(T) = 0$ there and the claim reads $T \le e$.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Appendix B.1, p. 30, first line ('using the fact that T^{(5/6)^K} ≤ e'); K defined in Algorithm 3, p. 15

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.IRT

theorem tau_Kirt_le_exp_one (T : ℝ) (hT : 1 ≤ T) :
    T ^ ((5 / 6 : ℝ) ^ Kirt T) ≤ Real.exp 1 := by sorry

end ResolvingNRM.IRT
