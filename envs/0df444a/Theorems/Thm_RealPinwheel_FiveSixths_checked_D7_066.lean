-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_066
-- name    : RealPinwheel.FiveSixths.checked_D7_066
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:23:35.368895+00:00
-- url     : https://prove2.me/theorems/ff1ae823-6f80-4078-ac4e-d8a9100d98d3
-- title:
--   Verified witness block D7_066
-- statement:
--   For every word in the exact witness block D7_066, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 352.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 352.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 1306–1345.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_066
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D7_066 : ∀ j : Fin 40, witnessCheck (witnessD7_066 j) = true ∧ (witnessD7_066 j).length ≤ 352 := by sorry
