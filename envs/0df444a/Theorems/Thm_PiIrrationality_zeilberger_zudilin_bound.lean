-- Prove2me | Theorems.Thm_PiIrrationality_zeilberger_zudilin_bound
-- name    : PiIrrationality.zeilberger_zudilin_bound
-- status  : Open
-- author  : @xuanji
-- created : 2026-10-03T19:36:44.871194+00:00
-- url     : https://prove2.me/theorems/220720d6-45c3-4bc4-8f43-294836e7fbe7
-- title:
--   The irrationality measure of π is at most 7.103205334138
-- statement:
--   The irrationality measure of $\pi$ is at most $7.103205334138$. For every real $\varepsilon>0$, there is a natural threshold $Q$, uniform in the integer numerator $p$ and positive natural denominator $q\ge Q$, such that $1/q^{7.103205334138+\varepsilon}<|\pi-p/q|$.
-- source:
--   D. Zeilberger, W. Zudilin, *The irrationality measure of $\pi$ is at most $7.103205334137\ldots$*, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419. https://arxiv.org/abs/1912.06345

import Definitions.Def_PiIrrationality_UpperBound

theorem PiIrrationality.zeilberger_zudilin_bound :
    PiIrrationality.UpperBound (7.103205334138 : ℝ) := by
  sorry
