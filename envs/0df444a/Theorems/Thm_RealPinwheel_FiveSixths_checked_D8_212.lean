-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_212
-- name    : RealPinwheel.FiveSixths.checked_D8_212
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T07:02:25.487724+00:00
-- url     : https://prove2.me/theorems/f0ce09c2-b25a-4ae0-8d25-d3ffe54198a8
-- title:
--   Verified witness block D8_212
-- statement:
--   For every word in the exact witness block D8_212, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 608.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 608.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2516–2540.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_212
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D8_212 : ∀ j : Fin 25, witnessCheck (witnessD8_212 j) = true ∧ (witnessD8_212 j).length ≤ 608 := by sorry
