-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_blocks_3
-- name    : TaoFivePrimes.theta_cert_blocks_3
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T14:22:37.375169+00:00
-- url     : https://prove2.me/theorems/f9205bf0-f652-46b9-b262-6bf30c94dedc
-- title:
--   theta cert blocks 3
-- statement:
--   Block verification, third chunk: the bound holds for every interval in the third group of 18 intervals.
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
theorem theta_cert_blocks_3 (ab : ℕ × ℕ) (hab : ab ∈ blk3) :
    ((min (ab.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (ab.2 + 1) 1420 : ℕ) : ℝ) <
      Chebyshev.theta ((ab.1 : ℕ) : ℝ) := by sorry
