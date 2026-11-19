-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_218
-- name    : RealPinwheel.FiveSixths.checked_D8_218
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T07:07:31.790769+00:00
-- url     : https://prove2.me/theorems/340665a4-5dd8-4255-bda1-8d9facab9ea9
-- title:
--   Verified witness block D8_218
-- statement:
--   For every word in the exact witness block D8_218, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 608.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 608.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2671–2697.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_218
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D8_218 : ∀ j : Fin 27, witnessCheck (witnessD8_218 j) = true ∧ (witnessD8_218 j).length ≤ 608 := by sorry
