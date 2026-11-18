-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_055
-- name    : RealPinwheel.FiveSixths.checked_D7_055
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:06:38.304549+00:00
-- url     : https://prove2.me/theorems/f0ace960-f3c0-4fd8-8a20-9ef51b5bce66
-- title:
--   Verified witness block D7_055
-- statement:
--   For every word in the exact witness block D7_055, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 352.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 352.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 943–971.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_055
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D7_055 : ∀ j : Fin 29, witnessCheck (witnessD7_055 j) = true ∧ (witnessD7_055 j).length ≤ 352 := by sorry
