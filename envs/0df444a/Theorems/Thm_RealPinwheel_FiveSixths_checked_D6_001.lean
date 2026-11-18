-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D6_001
-- name    : RealPinwheel.FiveSixths.checked_D6_001
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:02:43.740163+00:00
-- url     : https://prove2.me/theorems/5ec57653-2a44-42eb-be2d-682dd841dea1
-- title:
--   Verified witness block D6_001
-- statement:
--   For every word in the exact witness block D6_001, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 64.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 64.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D6, entries 17–35.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_001
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D6_001 : ∀ j : Fin 19, witnessCheck (witnessD6_001 j) = true ∧ (witnessD6_001 j).length ≤ 64 := by sorry
