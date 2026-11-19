-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_107
-- name    : RealPinwheel.FiveSixths.checked_P9_107
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T06:46:27.230194+00:00
-- url     : https://prove2.me/theorems/45defb3e-35fe-40a4-9811-07a78162f1d3
-- title:
--   Verified witness block P9_107
-- statement:
--   For every word in the exact witness block P9_107, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 1800.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 1800.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 603–612.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_107
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_P9_107 : ∀ j : Fin 10, witnessCheck (witnessP9_107 j) = true ∧ (witnessP9_107 j).length ≤ 1800 := by sorry
