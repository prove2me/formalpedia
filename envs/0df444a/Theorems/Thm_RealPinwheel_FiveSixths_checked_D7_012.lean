-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_012
-- name    : RealPinwheel.FiveSixths.checked_D7_012
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:22:42.032255+00:00
-- url     : https://prove2.me/theorems/fe2f9c9b-22f5-403f-98b3-fe987b5dbe6b
-- title:
--   Verified witness block D7_012
-- statement:
--   For every word in the exact witness block D7_012, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 352.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 352.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 97–107.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_012
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D7_012 : ∀ j : Fin 11, witnessCheck (witnessD7_012 j) = true ∧ (witnessD7_012 j).length ≤ 352 := by sorry
