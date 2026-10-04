-- Prove2me | Theorems.Thm_SecretaryWD_DiscLower_discounted_secretary_lower_bound_log
-- name    : SecretaryWD.DiscLower.discounted_secretary_lower_bound_log
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:36:12.159521+00:00
-- url     : https://prove2.me/theorems/93cd1a07-d283-447f-af5a-0c79572f20e5
-- title:
--   Theorem 4.3 — $\mathbb E[\mathrm{OPT}]/\mathbb E[A]\ge\frac1{40}\log n/\log\log n$ in the worst case
-- statement:
--   For every integer $c\ge2$, let $n=c^{4c}$ and let $d$ and $\mathcal I_1,\dots,\mathcal I_{2c}$ be the step discount and the instances of §4.1.1. For every randomized online stopping rule $A$ for horizon $n$ and discount $d$ there is some $t\in\{1,\dots,2c\}$ with
--
--   $$\frac1{40}\cdot\frac{\log n}{\log\log n}\cdot\mathbb E[A(\mathcal I_t)]\ <\ \mathbb E[\mathrm{OPT}(\mathcal I_t)],$$
--
--   where $\log$ is the natural logarithm. This is the $\Omega(\log n/\log\log n)$ form of Theorem 4.3, with an explicit constant, along the sequence of horizons $n=c^{4c}$.
--
--   **Formalization Note** The constant $1/40$ comes from $c/10$ and $\log n/\log\log n\le 4c$ for $c\ge2$ ($\log n=4c\log c$ and $\log\log n\ge\log c>0$). The statement is written multiplicatively, so $\mathbb E[A]=0$ is not a division-by-zero loophole. It is not claimed for horizons other than $c^{4c}$.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 7, Theorem 4.3; p. 6, Section 4.1.1 (L = c = Θ(log n / log log n))

import Mathlib
import Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
import Definitions.Def_SecretaryWD_DiscLower_HardInstances

namespace SecretaryWD.DiscLower

theorem discounted_secretary_lower_bound_log (c : ℕ) (hc : 2 ≤ c)
    (A : StoppingRule (horizon c)) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ 2 * c ∧
      1 / 40 * (Real.log (horizon c) / Real.log (Real.log (horizon c))) *
          expectedValue (discount c) (hardInstance c t) A <
        expectedOPT (discount c) (hardInstance c t) := by sorry

end SecretaryWD.DiscLower
