-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_127
-- name    : RealPinwheel.FiveSixths.checked_P9_127
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T07:11:29.051195+00:00
-- url     : https://prove2.me/theorems/a12bd2fd-b945-4c02-8fa9-d31a59f2ebc8
-- title:
--   Verified witness block P9_127
-- statement:
--   For every word in the exact witness block P9_127, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 1800.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 1800.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 831–843.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_127
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_P9_127 : ∀ j : Fin 13, witnessCheck (witnessP9_127 j) = true ∧ (witnessP9_127 j).length ≤ 1800 := by sorry
