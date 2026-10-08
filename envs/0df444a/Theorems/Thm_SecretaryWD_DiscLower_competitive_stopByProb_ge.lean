-- Prove2me | Theorems.Thm_SecretaryWD_DiscLower_competitive_stopByProb_ge
-- name    : SecretaryWD.DiscLower.competitive_stopByProb_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:35:51.014927+00:00
-- url     : https://prove2.me/theorems/47c30083-5f29-4358-a932-e177586d855d
-- title:
--   Lemma 4.2 — a $c/10$-competitive rule stops in the first $n_t$ steps of $\mathcal I_t$ with probability $\ge t/c$
-- statement:
--   Let $c\ge1$, $L=c$, $n=L^{4c}$, with the step discount $d$, the block ends $n_t=L^{2t}$ and the instances $\mathcal I_1,\dots,\mathcal I_{2c}$ of §4.1.1. Let $A$ be a randomized online stopping rule that is $c/10$-competitive on these instances:
--
--   $$\mathbb E[\mathrm{OPT}(\mathcal I_s)]\ \le\ \frac c{10}\,\mathbb E[A(\mathcal I_s)]\qquad(1\le s\le 2c).$$
--
--   Then for every $t$ with $1\le t\le 2c$,
--
--   $$\Pr_{\mathcal I_t}[A\text{ selects one of the first } n_t\text{ arrivals}]\ \ge\ \frac tc.$$
--
--   At $t=2c$ the bound is $2>1$, which is how Theorem 4.3 follows.
--
--   **Formalization Note** Competitiveness is assumed only on $\mathcal I_1,\dots,\mathcal I_{2c}$, which is all the proof uses. For $c<10$ the hypothesis cannot hold (since $\mathbb E[A]\le\mathbb E[\mathrm{OPT}]$ and $\mathbb E[\mathrm{OPT}(\mathcal I_s)]>0$), so the lemma has content for $c\ge10$.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 6, Lemma 4.2

import Mathlib
import Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
import Definitions.Def_SecretaryWD_DiscLower_HardInstances

namespace SecretaryWD.DiscLower

theorem competitive_stopByProb_ge (c : ℕ) (hc : 1 ≤ c) (A : StoppingRule (horizon c))
    (hA : ∀ s : ℕ, 1 ≤ s → s ≤ 2 * c →
      expectedOPT (discount c) (hardInstance c s) ≤
        (c : ℝ) / 10 * expectedValue (discount c) (hardInstance c s) A)
    (t : ℕ) (ht1 : 1 ≤ t) (ht2 : t ≤ 2 * c) :
    (t : ℝ) / c ≤ stopByProb (hardInstance c t) A (blockEnd c t) := by sorry

end SecretaryWD.DiscLower
