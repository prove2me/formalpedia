-- Prove2me | Theorems.Thm_PiIrrationality_chudnovsky_bound
-- name    : PiIrrationality.chudnovsky_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-03T05:49:19.991986+00:00
-- url     : https://prove2.me/theorems/06d04e2f-c2ad-434c-a9ba-332f6e66279c
-- title:
--   The irrationality measure of π is at most 19.8899945
-- statement:
--   The irrationality measure of $\pi$ is at most $19.8899945$. For every real $\varepsilon>0$, there is a natural threshold $Q$, uniform in the integer numerator $p$ and positive natural denominator $q\ge Q$, such that $1/q^{19.8899945+\varepsilon}<|\pi-p/q|$.
-- source:
--   G. V. Chudnovsky, *Hermite–Padé approximations to exponential functions and elementary estimates of the measure of irrationality of $\pi$*, Lecture Notes in Math. 925, Springer (1982), 299–322.

import Definitions.Def_PiIrrationality_UpperBound

theorem PiIrrationality.chudnovsky_bound :
    PiIrrationality.UpperBound (19.8899945 : ℝ) := by
  sorry
