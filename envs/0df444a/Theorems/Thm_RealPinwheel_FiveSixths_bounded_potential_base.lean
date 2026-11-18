-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_bounded_potential_base
-- name    : RealPinwheel.FiveSixths.bounded_potential_base
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-18T02:50:46.379561+00:00
-- url     : https://prove2.me/theorems/cbc64b2e-3df5-4cba-a49f-4827eb70b828
-- title:
--   Nine-task potential base with period at most 1800
-- statement:
--   Let $A$ be an ordered nine-task real-period instance with periods at least one. If its potential, the sum of the first eight reciprocal periods, satisfies $P(A)\le5/6$, then there exist a valid schedule $S$ and a positive integer period $L$ such that
--
--   $$L\le1800,\qquad S(t+L)=S(t)\quad(t\ge0).$$
--
--   This is the quantitative version of Lemma 6 established by the family $W_9$ in Table 1. It supplies the finite representation used when reversing the folds in Theorem 3.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, A Simple Computer-Assisted Proof of the 5/6-Bound for Real-Period Pinwheel Scheduling, STOC 2027 submission #885, October 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf, Lemma 6 and Section 4, Table 1 and proof of Theorem 3, printed pp. 10–11 (PDF pp. 11–12)

import Definitions.Def_RealPinwheel_FiveSixths_Instance
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.bounded_potential_base (A : Instance 9) (hP : potential A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
