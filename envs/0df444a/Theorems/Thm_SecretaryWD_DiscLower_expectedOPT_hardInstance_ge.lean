-- Prove2me | Theorems.Thm_SecretaryWD_DiscLower_expectedOPT_hardInstance_ge
-- name    : SecretaryWD.DiscLower.expectedOPT_hardInstance_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:35:31.395459+00:00
-- url     : https://prove2.me/theorems/30fbb73d-b887-4d5b-afd1-6b05a84e62f3
-- title:
--   Lemma 4.1 — $\mathbb E[\mathrm{OPT}(\mathcal I_t)]\ge(1-1/e)K^tL^{-t}$
-- statement:
--   Let $c\ge1$, $L=c$, $n=L^{4c}$, $K=n^2$, and let $d$ and $\mathcal I_1,\dots,\mathcal I_{2c}$ be the step discount and the instances of §4.1.1. For every $t$ with $1\le t\le 2c$, the expected offline optimum on $\mathcal I_t$ under a uniformly random arrival order satisfies
--
--   $$\mathbb E_\pi\Bigl[\max_{j} d(j)\,v_{\mathcal I_t}(\pi(j))\Bigr]\ \ge\ \Bigl(1-\frac1e\Bigr)K^tL^{-t}.$$
--
--   This lower bound on the benchmark is what makes $c/10$-competitiveness force the online rule to earn a constant fraction of $K^tL^{-t}$ on each instance.
--
--   **Formalization Note** The paper writes $OPT(\mathcal I_t)$ for $\mathbb E[\mathrm{OPT}(\mathcal I_t)]$, as the lemma's title says.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 6, Lemma 4.1

import Mathlib
import Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
import Definitions.Def_SecretaryWD_DiscLower_HardInstances

namespace SecretaryWD.DiscLower

theorem expectedOPT_hardInstance_ge (c t : ℕ) (hc : 1 ≤ c) (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * c) :
    (1 - 1 / Real.exp 1) * (bigK c : ℝ) ^ t * ((c : ℝ) ^ t)⁻¹ ≤
      expectedOPT (discount c) (hardInstance c t) := by sorry

end SecretaryWD.DiscLower
