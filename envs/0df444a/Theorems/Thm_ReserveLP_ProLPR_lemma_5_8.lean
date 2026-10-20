-- Prove2me | Theorems.Thm_ReserveLP_ProLPR_lemma_5_8
-- name    : ReserveLP.ProLPR.lemma_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:22.719598+00:00
-- url     : https://prove2.me/theorems/604ad7c8-34a0-4ddd-b373-2da1365bb2f1
-- title:
--   Lemma 5.8, p. 17 — OPT²(θ, k) ≤ 0.46 < 2(√2 − 1)e^(√2 − 2) for θ ∈ [0,1], k ≥ 2
-- statement:
--   For every $\theta\in[0,1]$ and every integer $k\ge2$,
--
--   $$\mathsf{OPT}^2(\theta,k)=e^{\theta-1}\Big[\Big(1-\frac{\theta}{k}\Big)^k+\theta(1-\theta)\Big(1-\frac{\theta}{k}\Big)^{k-1}\Big]\ \le\ 0.46\ <\ 2(\sqrt2-1)e^{\sqrt2-2}.$$
--
--   Together with Lemma 5.7, this shows that the second family of candidate maximizers of Problem (10) never beats the first.
-- source:
--   Derakhshan, Golrezaei, Paes Leme, LP-based Approximation for Personalized Reserve Prices, arXiv:1905.01526v5, p. 17, Lemma 5.8

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

namespace ReserveLP.ProLPR

theorem lemma_5_8 (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (hk : 2 ≤ k) :
    OPT2 θ k ≤ 0.46 ∧ (0.46 : ℝ) < cStar := by sorry

end ReserveLP.ProLPR
