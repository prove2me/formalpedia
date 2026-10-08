-- Prove2me | Theorems.Thm_PiIrrationality_hata_bound
-- name    : PiIrrationality.hata_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-03T19:36:31.839605+00:00
-- url     : https://prove2.me/theorems/424d91d3-a841-416e-b8e0-68b8d0182394
-- title:
--   The irrationality measure of π is at most 8.016046
-- statement:
--   The irrationality measure of $\pi$ is at most $8.016046$. For every real $\varepsilon>0$, there is a natural threshold $Q$, uniform in the integer numerator $p$ and positive natural denominator $q\ge Q$, such that $1/q^{8.016046+\varepsilon}<|\pi-p/q|$.
-- source:
--   M. Hata, *Rational approximations to $\pi$ and some other numbers*, Acta Arith. 63 (1993), no. 4, 335–349. http://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6344.pdf

import Definitions.Def_PiIrrationality_UpperBound

theorem PiIrrationality.hata_bound :
    PiIrrationality.UpperBound (8.016046 : ℝ) := by
  sorry
