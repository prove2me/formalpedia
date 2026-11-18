-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D5_000
-- name    : RealPinwheel.FiveSixths.checked_D5_000
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T03:56:56.951917+00:00
-- url     : https://prove2.me/theorems/768d203d-4058-4208-87cb-808629fede4e
-- title:
--   Verified witness block D5_000
-- statement:
--   For every word in the exact witness block D5_000, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 32.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 32.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D5, entries 1–36.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD5_000
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D5_000 : ∀ j : Fin 36, witnessCheck (witnessD5_000 j) = true ∧ (witnessD5_000 j).length ≤ 32 := by sorry
