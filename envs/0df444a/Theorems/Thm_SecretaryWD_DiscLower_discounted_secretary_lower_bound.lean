-- Prove2me | Theorems.Thm_SecretaryWD_DiscLower_discounted_secretary_lower_bound
-- name    : SecretaryWD.DiscLower.discounted_secretary_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T05:36:00.30823+00:00
-- url     : https://prove2.me/theorems/edd0183a-f51a-41e5-9b55-0c6bc3a0e286
-- title:
--   Theorem 4.3 — no online rule is $c/10$-competitive on $\mathcal I_1,\dots,\mathcal I_{2c}$ (horizon $n=c^{4c}$)
-- statement:
--   Let $c\ge1$ be an integer, $L=c$ and $n=L^{4c}$, and let $d$ be the step discount of §4.1.1 ($d(j)=L^{-t}$ on the block $n_{t-1}<j\le n_t$, $n_t=L^{2t}$) and $\mathcal I_1,\dots,\mathcal I_{2c}$ the instances of §4.1.1 (with $K=n^2$). For every randomized online stopping rule $A$ for horizon $n$ and discount $d$, which observes only the values of the elements as they arrive in uniformly random order, there is some $t\in\{1,\dots,2c\}$ with
--
--   $$c\cdot\mathbb E[A(\mathcal I_t)]\ <\ 10\cdot\mathbb E[\mathrm{OPT}(\mathcal I_t)].$$
--
--   Equivalently, no such rule is $c/10$-competitive on all of $\mathcal I_1,\dots,\mathcal I_{2c}$. Since $c=\Theta(\log n/\log\log n)$, this is the paper's lower bound $\mathbb E[\mathrm{OPT}]/\mathbb E[A]\ge\Omega(\log n/\log\log n)$ for the discounted secretary problem with arbitrary discount functions.
--
--   **Formalization Note** The constant $10$ is the one in the paper's proof ("if $A$ is $c/10$-competitive"). For $c<10$ the claim is immediate; no lower bound on $c$ is imposed. Times are 0-based (index $j$ is paper time $j+1$). The bound is claimed only for the horizons $n=c^{4c}$ that the paper constructs.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 7, Theorem 4.3 and its proof

import Mathlib
import Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
import Definitions.Def_SecretaryWD_DiscLower_HardInstances

namespace SecretaryWD.DiscLower

theorem discounted_secretary_lower_bound (c : ℕ) (hc : 1 ≤ c) (A : StoppingRule (horizon c)) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ 2 * c ∧
      (c : ℝ) * expectedValue (discount c) (hardInstance c t) A <
        10 * expectedOPT (discount c) (hardInstance c t) := by sorry

end SecretaryWD.DiscLower
