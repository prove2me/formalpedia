-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_observation_12
-- name    : RainbowEFX.Sublinear.observation_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:07.879399+00:00
-- url     : https://prove2.me/theorems/048e07dc-c3e6-4719-b618-500c73580a3c
-- title:
--   Observation 12, p. 12 — under assumption (*), |H_X| < 2n/(ε · d)
-- statement:
--   Throughout, $[n]$ is the set of agents and $M$ the set of $m$ indivisible goods; agent $i$ has an additive valuation $v_i$ with $v_i(S)=\sum_{g\in S}v_i(\{g\})\ge 0$. A (partial) allocation $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles, and $P = M\setminus\bigcup_i X_i$ is the set (pool) of unallocated goods.
--
--   Let $n\ge1$, $0<\varepsilon\le 1/2$, $d\ge 1$, and let $X$ be a $(1-\varepsilon)$-EFX allocation satisfying assumption (\*): the envy graph $E_X$ is acyclic and neither update rule U1 (Lemma 8) nor U2 (Lemma 9) applies. Let $H_X$ be the set of unallocated goods that are valuable ($v_i(g)>\varepsilon v_i(X_i)$) to at least $d+1$ agents. Then
--   $$
--   |H_X|<\frac{2n}{\varepsilon\cdot d}.
--   $$
--
--   This bounds the high-demand part of the pool; the low-demand part is bounded through the rainbow cycle number.
--
--   **Formalization Note** $n\ge 1$ is added: with $n=0$ the right-hand side is $0$ and the strict inequality fails. $d\ge1$ is the paper's standing choice of a positive integer $d$.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 12, Observation 12 and assumption (*)

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem observation_12 {n m : ℕ} (hn : 0 < n) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X) (hEFX : IsAlphaEFX (1 - ε) v X)
    (d : ℕ) (hd : 1 ≤ d) (hstar : Star ε v X) :
    ((HX ε v X d).card : ℝ) < 2 * n / (ε * d) := by sorry

end RainbowEFX.Sublinear
