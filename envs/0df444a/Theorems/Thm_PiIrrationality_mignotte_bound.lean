-- Prove2me | Theorems.Thm_PiIrrationality_mignotte_bound
-- name    : PiIrrationality.mignotte_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-03T05:49:04.398803+00:00
-- url     : https://prove2.me/theorems/9aa67ee4-a533-4a45-89d5-48ff718b63b0
-- title:
--   The irrationality measure of π is at most 20.6
-- statement:
--   The irrationality measure of $\pi$ is at most $20.6$. For every real $\varepsilon>0$, there is a natural threshold $Q$, uniform in the integer numerator $p$ and positive natural denominator $q\ge Q$, such that $1/q^{20.6+\varepsilon}<|\pi-p/q|$.
-- source:
--   M. Mignotte, *Approximations rationnelles de $\pi$ et quelques autres nombres*, Mém. Soc. Math. France 37 (1974), 121–132. https://doi.org/10.24033/msmf.139

import Definitions.Def_PiIrrationality_UpperBound

theorem PiIrrationality.mignotte_bound :
    PiIrrationality.UpperBound (20.6 : ℝ) := by
  sorry
