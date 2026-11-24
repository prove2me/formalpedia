-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_blocks_4
-- name    : TaoFivePrimes.theta_cert_blocks_4
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T14:22:47.474905+00:00
-- url     : https://prove2.me/theorems/b61cf1aa-c73d-427d-8fea-b85195c7d308
-- title:
--   theta cert blocks 4
-- statement:
--   Block verification, fourth chunk: the bound holds for every interval in the fourth group of 18 intervals (near the top of the range).
--
--   Same verification as the first chunk; the top block $(1413,1420)$ uses the clamped target $T = 1420$.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; p. 82, Theorem 19 (finite window), used in the '288' chain of the Lemma 15 proof, p. 89. https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
import Theorems.Thm_TaoFivePrimes_theta_cert_plist_eq
import Theorems.Thm_TaoFivePrimes_theta_cert_primesLE_eq
import Theorems.Thm_TaoFivePrimes_theta_cert_clbZ_le_log

namespace TaoFivePrimes
theorem theta_cert_blocks_4 (ab : ℕ × ℕ) (hab : ab ∈ blk4) :
    ((min (ab.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (ab.2 + 1) 1420 : ℕ) : ℝ) <
      Chebyshev.theta ((ab.1 : ℕ) : ℝ) := by sorry
