-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_gss_scalar_nonpos
-- name    : QuantumMaxCutEnergy.gss_scalar_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T04:51:38.025633+00:00
-- url     : https://prove2.me/theorems/50829977-f99c-4c01-a2eb-b672710c8175
-- title:
--   GSS25 scalar on the negative half $s\\in[-1/3,0]$ (0.603 mixing step)
-- statement:
--   The negative half of Gribling–Sinjorgo–Sotirov's mixing scalar (the 0.603 analysis).
--
--   For $s \in [-1/3,0]$,
--   $$0.6031\cdot\frac{1+3s}{2} \;\le\; 0.724\cdot\frac{1+0.8488s+0.08488s^3}{2} + 0.276\Bigl(\frac12 + \frac32\cdot\frac{14}{15}\max\Bigl(\frac{3s-1}{2},0\Bigr)\Bigr).$$
--   Here the matching term $\max((3s-1)/2,0)$ vanishes and the bound reduces to the product term; with the platform's proved `gss25_strict_scalar` on $s\in[0,1]$ this covers the full admissible range $[-1/3,1]$ of the level-2 relaxation. **Role.** The per-edge numeric step of the 0.603 entry's level-13 analysis.
-- source:
--   Scalar step of Eunou Lee and Ojas Parekh, ICALP 2024, https://arxiv.org/abs/2401.03616 Theorem 2 / Sander Gribling, Lennart Sinjorgo, Renata Sotirov, https://arxiv.org/abs/2504.11120 Theorem 3.11; full-range completion via the effective range s in [-1/3,1] of the level-2 moment constraints

import Mathlib

theorem QuantumMaxCutEnergy.gss_scalar_nonpos (s : ℝ) (h1 : -1 / 3 ≤ s) (h2 : s ≤ 0) :
    (0.6031 : ℝ) * ((1 + 3 * s) / 2) ≤
      0.724 * ((1 + 0.8488 * s + 0.08488 * s ^ 3) / 2) +
        (1 - 0.724) * (1 / 2 + (3 / 2) * (14 / 15) * max ((3 * s - 1) / 2) 0) := by sorry
