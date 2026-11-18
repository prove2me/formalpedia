-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D7_026
-- name    : RealPinwheel.FiveSixths.checked_D7_026
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:39:29.765505+00:00
-- url     : https://prove2.me/theorems/688e05dc-ef1e-4531-9c07-f65f531965f4
-- title:
--   Verified witness block D7_026
-- statement:
--   For every word in the exact witness block D7_026, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 352.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 352.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D7, entries 290–306.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_026
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D7_026 : ∀ j : Fin 17, witnessCheck (witnessD7_026 j) = true ∧ (witnessD7_026 j).length ≤ 352 := by sorry
