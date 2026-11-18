-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_010
-- name    : RealPinwheel.FiveSixths.checked_D7_010
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:22:00.526204+00:00
-- url     : https://prove2.me/theorems/3ef7659c-5a9e-4979-9ecf-0b1841ecc0fa
-- title:
--   Verified witness block D7_010
-- statement:
--   For every word in the exact witness block D7_010, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 352.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 352.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 76–85.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_010
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D7_010 : ∀ j : Fin 10, witnessCheck (witnessD7_010 j) = true ∧ (witnessD7_010 j).length ≤ 352 := by sorry
