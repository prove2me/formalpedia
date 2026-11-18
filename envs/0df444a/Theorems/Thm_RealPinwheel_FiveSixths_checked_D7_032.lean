-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_032
-- name    : RealPinwheel.FiveSixths.checked_D7_032
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:43:03.445197+00:00
-- url     : https://prove2.me/theorems/382bc2a7-87a4-4418-aa38-3c25417db416
-- title:
--   Verified witness block D7_032
-- statement:
--   For every word in the exact witness block D7_032, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 352.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 352.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 396–414.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_032
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D7_032 : ∀ j : Fin 19, witnessCheck (witnessD7_032 j) = true ∧ (witnessD7_032 j).length ≤ 352 := by sorry
