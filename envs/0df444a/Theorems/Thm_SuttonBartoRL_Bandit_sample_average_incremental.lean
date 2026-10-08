-- Prove2me | Theorems.Thm_SuttonBartoRL_Bandit_sample_average_incremental
-- name    : SuttonBartoRL.Bandit.sample_average_incremental
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T02:48:44.018868+00:00
-- url     : https://prove2.me/theorems/9de02399-7d7f-4c2b-9873-ecd14d6e16ff
-- title:
--   Eq. (2.3) — incremental computation of the sample average
-- statement:
--   Let $R_1, R_2, \dots$ be real rewards and let $Q_n$ be the sample average of the first $n-1$ of them, with an arbitrary initial value $Q_1$. Then for every $n \ge 1$,
--
--   $$
--   Q_{n+1} = Q_n + \frac{1}{n}\bigl[R_n - Q_n\bigr].
--   $$
--
--   In particular, for $n = 1$ the formula gives $Q_2 = R_1$ whatever $Q_1$ is.
--
--   This is the update rule that lets a bandit algorithm keep an exact sample average with constant memory; it is the prototype of the "NewEstimate ← OldEstimate + StepSize [Target − OldEstimate]" rule (2.4) used throughout the book.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (2.3) and the sentence after it, p. 31

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_IncrementalEstimates

namespace SuttonBartoRL.Bandit

theorem sample_average_incremental (R : ℕ → ℝ) (Q₁ : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    sampleAverage R Q₁ (n + 1)
      = sampleAverage R Q₁ n + (1 / (n : ℝ)) * (R n - sampleAverage R Q₁ n) := by sorry

end SuttonBartoRL.Bandit
