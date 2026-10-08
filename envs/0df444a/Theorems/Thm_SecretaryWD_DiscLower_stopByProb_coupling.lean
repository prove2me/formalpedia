-- Prove2me | Theorems.Thm_SecretaryWD_DiscLower_stopByProb_coupling
-- name    : SecretaryWD.DiscLower.stopByProb_coupling
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:35:55.561536+00:00
-- url     : https://prove2.me/theorems/ed5547ac-cab9-4a83-83bd-84a843b280f0
-- title:
--   Proof of Lemma 4.2 — $\mathcal I_t$ and $\mathcal I_{t+1}$ are indistinguishable in the first $n_t$ steps up to probability $1/L^2$
-- statement:
--   Let $c\ge1$, $L=c$, $n=L^{4c}$, with $n_t=L^{2t}$ and the instances $\mathcal I_t$ of §4.1.1. For every $t$ with $1\le t<2c$ and every randomized online stopping rule $A$ (which observes values only),
--
--   $$\Pr_{\mathcal I_{t+1}}[A\text{ selects among the first } n_t\text{ arrivals}]\ \ge\ \Pr_{\mathcal I_t}[A\text{ selects among the first } n_t\text{ arrivals}]-\frac1{L^2}.$$
--
--   The two instances differ only in $n/n_{t+1}$ elements, and the chance that one of them arrives in the first $n_t$ steps is at most $n_t/n_{t+1}=L^{-2}$. This is the step that carries the induction of Lemma 4.2 from $\mathcal I_t$ to $\mathcal I_{t+1}$.
--
--   **Formalization Note** The statement holds for every rule, with no competitiveness hypothesis. It is stated in difference form; the paper's sentence "with probability at least $(1-1/L^2)(t/c)$" is a different (product) form and is not what is claimed here.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 6, proof of Lemma 4.2 (inductive step)

import Mathlib
import Definitions.Def_SecretaryWD_DiscLower_DiscountedSecretary
import Definitions.Def_SecretaryWD_DiscLower_HardInstances

namespace SecretaryWD.DiscLower

theorem stopByProb_coupling (c t : ℕ) (hc : 1 ≤ c) (ht1 : 1 ≤ t) (ht2 : t < 2 * c)
    (A : StoppingRule (horizon c)) :
    stopByProb (hardInstance c t) A (blockEnd c t) - 1 / (c : ℝ) ^ 2 ≤
      stopByProb (hardInstance c (t + 1)) A (blockEnd c t) := by sorry

end SecretaryWD.DiscLower
