-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm2020_scalar_ratio_053
-- name    : QuantumMaxCutEnergy.agm2020_scalar_ratio_053
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T00:54:56.199245+00:00
-- url     : https://prove2.me/theorems/1552fab5-9597-444e-a868-0389294b6f32
-- title:
--   The published 0.53 scalar bound
-- statement:
--   For real numbers $0\le x\le y\le1$,
--
--   $$\frac{\max\{2y,3x+0.98,(0.956/3)(4+x+y)\}}{2+x+y}\ge0.53.$$
--
--   This is the scalar inequality in the published Eq. (30). It verifies one numerical step of the approximation analysis, with exact rational constants. It does not establish the complete polynomial-time algorithm.
-- source:
--   Anshu, Gosset, and Morenz, TQC 2020, Eq. (30), p. 7:10, in the proof of Theorem 3. https://doi.org/10.4230/LIPIcs.TQC.2020.7 . This is the scalar inequality only; state energies and runtime remain separate proof obligations.

import Mathlib

theorem QuantumMaxCutEnergy.agm2020_scalar_ratio_053 (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    (0.53 : ℝ) ≤
      max (2 * y) (max (3 * x + 0.98) ((0.956 / 3) * (4 + x + y))) /
        (2 + x + y) := by sorry
