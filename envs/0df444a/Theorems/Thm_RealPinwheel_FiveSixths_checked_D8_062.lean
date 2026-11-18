-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_062
-- name    : RealPinwheel.FiveSixths.checked_D8_062
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:59:14.057351+00:00
-- url     : https://prove2.me/theorems/216b47ab-6365-4a3e-af6d-c2636556fc65
-- title:
--   Verified witness block D8_062
-- statement:
--   For every word in the exact witness block D8_062, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 608.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 608.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 304–311.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_062
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D8_062 : ∀ j : Fin 8, witnessCheck (witnessD8_062 j) = true ∧ (witnessD8_062 j).length ≤ 608 := by sorry
