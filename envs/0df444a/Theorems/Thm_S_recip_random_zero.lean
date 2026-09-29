-- Prove2me | Theorems.Thm_S_recip_random_zero
-- name    : S_recip_random_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T06:27:05.743736+00:00
-- url     : https://prove2.me/theorems/7d2d3399-01ea-4346-abd8-3f944382b049
-- title:
--   Randomized series recovers the classical series on the zero path
-- statement:
--   On the identically-zero phase path the randomized partial series agrees with the classical one: $S_{\text{recip}}^{\text{rand}}(N, P, s, 0) = S_{\text{class}}(N, s)$, since the corrector collapses to $1$ term-by-term.

import Mathlib
import Definitions.Def_timepiece_corrector
open Complex Finset Filter Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius ComplexConjugate

theorem S_recip_random_zero (N P : ℕ) (s : ℂ) :
    S_recip_random N P s (fun _ ↦ 0) = S_classical N s := by sorry
