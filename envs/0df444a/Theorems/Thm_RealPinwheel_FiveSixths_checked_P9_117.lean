-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_117
-- name    : RealPinwheel.FiveSixths.checked_P9_117
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T06:54:35.746258+00:00
-- url     : https://prove2.me/theorems/df035b7f-02ab-4a71-952b-7a0b94c316c7
-- title:
--   Verified witness block P9_117
-- statement:
--   For every word in the exact witness block P9_117, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 1800.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 1800.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 712–722.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_117
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_P9_117 : ∀ j : Fin 11, witnessCheck (witnessP9_117 j) = true ∧ (witnessP9_117 j).length ≤ 1800 := by sorry
