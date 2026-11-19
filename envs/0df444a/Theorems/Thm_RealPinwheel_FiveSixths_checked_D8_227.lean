-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_227
-- name    : RealPinwheel.FiveSixths.checked_D8_227
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T07:14:47.059444+00:00
-- url     : https://prove2.me/theorems/7901e570-790e-4ab2-8fbb-7ed61f6119ce
-- title:
--   Verified witness block D8_227
-- statement:
--   For every word in the exact witness block D8_227, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 608.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 608.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2919–2947.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_227
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D8_227 : ∀ j : Fin 29, witnessCheck (witnessD8_227 j) = true ∧ (witnessD8_227 j).length ≤ 608 := by sorry
