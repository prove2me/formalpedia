-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_013
-- name    : RealPinwheel.FiveSixths.checked_D7_013
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:25:44.137279+00:00
-- url     : https://prove2.me/theorems/740dd019-8779-4ec2-96c2-40c86f1b8ddb
-- title:
--   Verified witness block D7_013
-- statement:
--   For every word in the exact witness block D7_013, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 352.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 352.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 108–118.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_013
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D7_013 : ∀ j : Fin 11, witnessCheck (witnessD7_013 j) = true ∧ (witnessD7_013 j).length ≤ 352 := by sorry
