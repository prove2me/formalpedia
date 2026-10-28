-- Prove2me | Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_above_exp136
-- name    : TaoFivePrimes.schoenfeld_psi_error_above_exp136
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T16:48:48.306108+00:00
-- url     : https://prove2.me/theorems/62a9c5ac-9a3d-4b38-b7fc-b509eb3cd477
-- title:
--   Chebyshev psi error beyond exp(136)
-- statement:
--   Let $\psi(y)=\sum_{n\le y}\Lambda(n)$ be the second Chebyshev function. For every real $y\ge e^{136}$,
--
--   $$|\psi(y)-y|\le\frac{y}{40\log y}.$$
--
--   This is an unconditional tail of the explicit Chebyshev estimate used in Tao’s Lemma 4.3. The threshold is inclusive.
-- source:
--   T. Tao, arXiv:1201.6656v4, Section 4, proof of Lemma 4.3, https://arxiv.org/html/1201.6656v4#S4. The exp(136) range is a restriction of the estimate cited there. The proof is a specialization and extension of the published Prove2Me proof of ExplicitPNT.DusartTable1.Modules.PowerQuarterPsi, submission e6bfa461-8c34-4d5b-878e-1ab914126846, using the proved PowerQuarterSmoothed theorem ff5adaac-fb81-4f63-8109-19ee20838b95.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Exp

theorem TaoFivePrimes.schoenfeld_psi_error_above_exp136 (y : ℝ) (hy : Real.exp 136 ≤ y) : |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by sorry
