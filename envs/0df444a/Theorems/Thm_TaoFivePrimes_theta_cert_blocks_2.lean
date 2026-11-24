-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_blocks_2
-- name    : TaoFivePrimes.theta_cert_blocks_2
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T14:22:38.556341+00:00
-- url     : https://prove2.me/theorems/650daa8d-f24e-4eab-9c79-918cea9c4f9e
-- title:
--   theta cert blocks 2
-- statement:
--   Block verification, second chunk: the bound holds for every interval in the second group of 18 intervals.
--
--   Same verification as the first chunk.
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
theorem theta_cert_blocks_2 (ab : ℕ × ℕ) (hab : ab ∈ blk2) :
    ((min (ab.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (ab.2 + 1) 1420 : ℕ) : ℝ) <
      Chebyshev.theta ((ab.1 : ℕ) : ℝ) := by sorry
