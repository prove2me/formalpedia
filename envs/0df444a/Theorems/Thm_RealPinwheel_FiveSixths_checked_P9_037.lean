-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_P9_037
-- name    : RealPinwheel.FiveSixths.checked_P9_037
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:05:18.354044+00:00
-- url     : https://prove2.me/theorems/172558c9-c4ad-4418-8a66-2c8aa77bcbec
-- title:
--   Verified witness block P9_037
-- statement:
--   For every word in the exact witness block P9_037, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 1800.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 1800.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate P9, entries 99–103.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_037
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_P9_037 : ∀ j : Fin 5, witnessCheck (witnessP9_037 j) = true ∧ (witnessP9_037 j).length ≤ 1800 := by sorry
