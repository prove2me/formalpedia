-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_145
-- name    : RealPinwheel.FiveSixths.checked_D8_145
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T06:10:34.948464+00:00
-- url     : https://prove2.me/theorems/43f24ca8-e80b-4de9-81f0-82c4d62c74f6
-- title:
--   Verified witness block D8_145
-- statement:
--   For every word in the exact witness block D8_145, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 608.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 608.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 1232–1246.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_145
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D8_145 : ∀ j : Fin 15, witnessCheck (witnessD8_145 j) = true ∧ (witnessD8_145 j).length ≤ 608 := by sorry
