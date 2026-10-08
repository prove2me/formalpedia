-- Prove2me | Theorems.Thm_PiIrrationality_rhin_viola_bound
-- name    : PiIrrationality.rhin_viola_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-03T19:36:29.13438+00:00
-- url     : https://prove2.me/theorems/bda7f199-9603-4c9e-8825-e30a14d70f09
-- title:
--   The irrationality measure of π is at most 14.797074
-- statement:
--   The irrationality measure of $\pi$ is at most $14.797074$. For every real $\varepsilon>0$, there is a natural threshold $Q$, uniform in the integer numerator $p$ and positive natural denominator $q\ge Q$, such that $1/q^{14.797074+\varepsilon}<|\pi-p/q|$.
-- source:
--   G. Rhin, C. Viola, *On the irrationality measure of $\zeta(2)$*, Ann. Inst. Fourier (Grenoble) 43 (1993), no. 1, 85–109. https://doi.org/10.5802/aif.1322

import Definitions.Def_PiIrrationality_UpperBound

theorem PiIrrationality.rhin_viola_bound :
    PiIrrationality.UpperBound (14.797074 : ℝ) := by
  sorry
