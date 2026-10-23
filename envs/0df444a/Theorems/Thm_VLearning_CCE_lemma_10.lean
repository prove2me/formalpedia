-- Prove2me | Theorems.Thm_VLearning_CCE_lemma_10
-- name    : VLearning.CCE.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:50.940564+00:00
-- url     : https://prove2.me/theorems/a312d19d-f5fb-423d-8054-5a22651f882c
-- title:
--   Lemma 10, p. 19 — properties of the weights α^i_t
-- statement:
--   Let $H\ge 1$ and let $\alpha^i_t$ be the weights (3) of the learning rate $\alpha_t=(H+1)/(H+t)$. Then:
--
--   1. for every $t\ge1$,
--   $$\frac1{\sqrt t}\le\sum_{i=1}^t\frac{\alpha^i_t}{\sqrt i}\le\frac2{\sqrt t},\qquad \frac1t\le\sum_{i=1}^t\frac{\alpha^i_t}{i}\le\frac2t;$$
--   2. for every $t\ge1$, $\max_{i\in[t]}\alpha^i_t\le 2H/t$ and $\sum_{i=1}^t(\alpha^i_t)^2\le 2H/t$;
--   3. for every $i\ge1$, $\sum_{t=i}^\infty\alpha^i_t=1+1/H$.
--
--   These are the properties of the Q-learning learning rate used throughout the analysis of V-learning; item 3 controls how often an earlier update is counted in later estimates.
--
--   **Formalization Note** Item 3 is stated as the convergence of the series $\sum_{n\ge0}\alpha^i_{i+n}$ to $1+1/H$.
-- source:
--   Jin, Liu, Wang & Yu, V-Learning—A Simple, Efficient, Decentralized Algorithm for Multiagent RL, arXiv:2110.14555v1, p. 19, Lemma 10

import Mathlib
import Definitions.Def_VLearning_CCE_WeightedBandit

namespace VLearning.CCE

open Finset

/-- Lemma 10 (p. 19): properties of the weights `α^i_t` of (3), for `H ≥ 1`. -/
theorem lemma_10 (H : ℕ) (hH : 1 ≤ H) :
    (∀ t : ℕ, 1 ≤ t →
      1 / Real.sqrt t ≤ ∑ i ∈ Icc 1 t, lrW H t i / Real.sqrt i ∧
      ∑ i ∈ Icc 1 t, lrW H t i / Real.sqrt i ≤ 2 / Real.sqrt t ∧
      1 / (t : ℝ) ≤ ∑ i ∈ Icc 1 t, lrW H t i / i ∧
      ∑ i ∈ Icc 1 t, lrW H t i / i ≤ 2 / (t : ℝ)) ∧
    (∀ t : ℕ, 1 ≤ t →
      (∀ i ∈ Icc 1 t, lrW H t i ≤ 2 * (H : ℝ) / t) ∧
      ∑ i ∈ Icc 1 t, lrW H t i ^ 2 ≤ 2 * (H : ℝ) / t) ∧
    (∀ i : ℕ, 1 ≤ i → HasSum (fun n : ℕ => lrW H (i + n) i) (1 + 1 / (H : ℝ))) := by sorry

end VLearning.CCE
