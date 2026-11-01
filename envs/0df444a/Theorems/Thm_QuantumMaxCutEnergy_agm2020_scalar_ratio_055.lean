-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_agm2020_scalar_ratio_055
-- name    : QuantumMaxCutEnergy.agm2020_scalar_ratio_055
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T00:54:55.806988+00:00
-- url     : https://prove2.me/theorems/e9681a36-0891-4b76-9285-d9fa8c26d7eb
-- title:
--   The published 0.55 scalar bound
-- statement:
--   For real numbers $0\le x\le y\le1$,
--
--   $$\frac{\max\{2y,3x+1,(4+x+y)/3\}}{2+x+y}\ge0.55.$$
--
--   This is the scalar inequality in the published Eq. (29). It certifies the numerical combination step in the analysis; constructing states and proving algorithmic running time are separate obligations.
-- source:
--   Anshu, Gosset, and Morenz, TQC 2020, Eq. (29), p. 7:10, in the proof of Theorem 3. https://doi.org/10.4230/LIPIcs.TQC.2020.7 . All decimals are exact rationals; this is a scalar estimate, not an algorithm theorem.

import Mathlib

theorem QuantumMaxCutEnergy.agm2020_scalar_ratio_055 (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    (0.55 : ℝ) ≤
      max (2 * y) (max (3 * x + 1) ((4 + x + y) / 3)) / (2 + x + y) := by sorry
