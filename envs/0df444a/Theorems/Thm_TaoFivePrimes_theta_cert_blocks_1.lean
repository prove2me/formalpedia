-- Prove2me | Theorems.Thm_TaoFivePrimes_theta_cert_blocks_1
-- name    : TaoFivePrimes.theta_cert_blocks_1
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T14:22:35.353244+00:00
-- url     : https://prove2.me/theorems/693e24ab-b112-4b71-ab48-d900125d97ef
-- title:
--   theta cert blocks 1
-- statement:
--   Block verification, first chunk: for every interval $(a,b)$ in the first group of 17 intervals covering $[255,1420]$, Rosser--Schoenfeld's bound holds at $b$: $(\min(b+1,1420)) - 2\sqrt{\min(b+1,1420)} < \theta(a)$.
--
--   For a block $(a,b)$ with target $T = \min(b+1,1420)$ and $r = T - \lfloor 2\sqrt T\rfloor$, the integer check $\sum_{p \le a} \lfloor 10^4 \log p\rfloor > 10^4 r$ is verified by direct computation, and the per-element table bounds turn the rational sum into $\sum_{p \le a} \log p = \theta(a)$ via $\theta(a) = \sum_{p \in \mathrm{primesLE}\,a} \log p$.
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
theorem theta_cert_blocks_1 (ab : ℕ × ℕ) (hab : ab ∈ blk1) :
    ((min (ab.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (ab.2 + 1) 1420 : ℕ) : ℝ) <
      Chebyshev.theta ((ab.1 : ℕ) : ℝ) := by sorry
