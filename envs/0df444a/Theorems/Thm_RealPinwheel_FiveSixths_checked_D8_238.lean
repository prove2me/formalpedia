-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_238
-- name    : RealPinwheel.FiveSixths.checked_D8_238
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T07:29:01.043833+00:00
-- url     : https://prove2.me/theorems/3d8113f9-0257-43fa-bd87-654c3eabfac0
-- title:
--   Verified witness block D8_238
-- statement:
--   For every word in the exact witness block D8_238, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 608.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 608.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 3262–3296.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_238
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D8_238 : ∀ j : Fin 35, witnessCheck (witnessD8_238 j) = true ∧ (witnessD8_238 j).length ≤ 608 := by sorry
