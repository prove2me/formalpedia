-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_scalar_full_0595
-- name    : QuantumMaxCutEnergy.scalar_full_0595
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T04:50:17.374294+00:00
-- url     : https://prove2.me/theorems/6d8e3cc8-5049-49bb-bff4-d31a835ce675
-- title:
--   LP24 scalar on the full range $s\\in[-1/3,1]$ (0.595 mixing inequality)
-- statement:
--   Completion of Lee–Parekh's mixing scalar to the full admissible range of the level-2 analysis.
--
--   The feasible edge parameter of the level-2 Quantum Max-Cut relaxation ranges over $s \in [-1/3, 1]$, while the platform's `lp24_strict_scalar` certifies the mixing inequality only for $s \in [0,1]$. This theorem supplies the negative half $s \in [-1/3, 0]$ — where the matching (positive-excess) term $\max((3s-1)/2,0)$ vanishes and the product term alone carries the inequality — and assembles the two halves, so that
--   $$0.5955\cdot\frac{1+3s}{2} \;\le\; 0.672\cdot\frac{1+0.8488s+0.08488s^3}{2} + 0.328\Bigl(\frac12 + \frac32\cdot\frac45\max\Bigl(\frac{3s-1}{2},0\Bigr)\Bigr)$$
--   holds for every $s \in [-1/3,1]$, given its positive half. **Role.** The per-edge numeric endgame of the 0.595 entry's analysis: with this, the mixing step of the LP24 algorithm is certified on the whole range the relaxation permits.
-- source:
--   Scalar step of Eunou Lee and Ojas Parekh, ICALP 2024, https://arxiv.org/abs/2401.03616 Theorem 2 / Sander Gribling, Lennart Sinjorgo, Renata Sotirov, https://arxiv.org/abs/2504.11120 Theorem 3.11; full-range completion via the effective range s in [-1/3,1] of the level-2 moment constraints

import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.scalar_full_0595 (hpos : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (0.5955 : ℝ) * ((1 + 3 * s) / 2) ≤
        0.672 * ((1 + 0.8488 * s + 0.08488 * s ^ 3) / 2) +
          (1 - 0.672) * (1 / 2 + (3 / 2) * (4 / 5) * max ((3 * s - 1) / 2) 0))
    (s : ℝ) (h : -1 / 3 ≤ s) (h' : s ≤ 1) :
    (0.5955 : ℝ) * ((1 + 3 * s) / 2) ≤
      0.672 * ((1 + 0.8488 * s + 0.08488 * s ^ 3) / 2) +
        (1 - 0.672) * (1 / 2 + (3 / 2) * (4 / 5) * max ((3 * s - 1) / 2) 0) := by sorry
