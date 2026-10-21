-- Prove2me | Theorems.Thm_PoWMining_Investment_eq_5_2
-- name    : PoWMining.Investment.eq_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:43.772382+00:00
-- url     : https://prove2.me/theorems/72a27068-4b48-4f03-95bb-8942871aaf30
-- title:
--   (5.2), p. 22 — investing min{1/η,1} reduces the cost by (c̃_i − c̃_0)/(2η) or (1 − η/2)(c̃_i − c̃_0), and min{1/η,1} uniquely minimizes c_i on [0,1]
-- statement:
--   Under the standing assumptions of the investment model, let $\bar\beta=\min\{1/\eta,1\}$ (equal to $1$ when $\eta=0$) and let $c_i(\beta_i)$ be the cost (3.1)–(3.2). Then the reduction in miner $i$'s cost-per-hash from investing $\bar\beta$ is
--
--   $$
--   I_i:=c_i(0)-c_i(\bar\beta)=\begin{cases}\dfrac{1}{2\eta}(\tilde c_i-\tilde c_0), & \eta>1,\\[6pt] \Big(1-\dfrac{\eta}{2}\Big)(\tilde c_i-\tilde c_0), & \eta\le1.\end{cases}
--   $$
--
--   Moreover $\bar\beta\in[0,1]$, and $\bar\beta$ is the unique minimizer of $b\mapsto c_i(b)$ over $[0,1]$: $c_i(\bar\beta)<c_i(b)$ for every $b\in[0,1]$ with $b\ne\bar\beta$.
--
--   The second part is the cost minimization the proof of Proposition 5.1 invokes on p. 44 ("the optimal investment of an active miner $i$ is obtained by minimizing the cost $c_i(\beta_i)$").
--
--   **Formalization Note** The cost after investment is evaluated at the constant profile $\beta_j=\bar\beta$; $c_i$ depends only on $\beta_i$. The uniqueness of the minimizer uses the standing addition $\tilde c_0<\tilde c_i$; without it $c_i$ would be constant.
-- source:
--   Capponi, Ólafsson & Alsabah, Proof-of-Work Cryptocurrencies: Does Mining Technology Undermine Decentralization?, arXiv:2106.09783v1, p. 22, (5.2); p. 44, proof of Proposition 5.1

import Mathlib
import Definitions.Def_PoWMining_Investment_Model

namespace PoWMining.Investment

/-- (5.2), p. 22: investing `min{1/η, 1}` reduces miner `i`'s cost-per-hash by
`(c̃_i - c̃_0)/(2η)` if `η > 1` and by `(1 - η/2)(c̃_i - c̃_0)` if `η ≤ 1`; moreover
`min{1/η, 1} ∈ [0, 1]` is the unique minimizer of `b ↦ c_i(b)` on `[0, 1]` (the cost
minimization used on p. 44). -/
theorem eq_5_2 {N : ℕ} (P : InvParams N) (hP : P.Standing) (i : Fin N) :
    cost P 0 i - cost P (fun _ => betaBar P) i =
        (if 1 < P.η then (P.ct i - P.c0) / (2 * P.η) else (1 - P.η / 2) * (P.ct i - P.c0)) ∧
      betaBar P ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ b ∈ Set.Icc (0 : ℝ) 1, b ≠ betaBar P →
        cost P (fun _ => betaBar P) i < cost P (fun _ => b) i := by sorry

end PoWMining.Investment
