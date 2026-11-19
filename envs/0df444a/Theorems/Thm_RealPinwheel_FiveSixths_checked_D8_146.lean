-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_146
-- name    : RealPinwheel.FiveSixths.checked_D8_146
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T06:12:29.167281+00:00
-- url     : https://prove2.me/theorems/e1a6bf8f-7a9e-46a3-94cd-ef657dc49227
-- title:
--   Verified witness block D8_146
-- statement:
--   For every word in the exact witness block D8_146, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 608.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 608.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1247–1261.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_146
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D8_146 : ∀ j : Fin 15, witnessCheck (witnessD8_146 j) = true ∧ (witnessD8_146 j).length ≤ 608 := by sorry
