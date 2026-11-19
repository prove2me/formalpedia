-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_205
-- name    : RealPinwheel.FiveSixths.checked_D8_205
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T06:53:49.326587+00:00
-- url     : https://prove2.me/theorems/9fdf4c1e-1a6a-4266-bb29-df077e1f7e7c
-- title:
--   Verified witness block D8_205
-- statement:
--   For every word in the exact witness block D8_205, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 608.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 608.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 2344–2366.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_205
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D8_205 : ∀ j : Fin 23, witnessCheck (witnessD8_205 j) = true ∧ (witnessD8_205 j).length ≤ 608 := by sorry
