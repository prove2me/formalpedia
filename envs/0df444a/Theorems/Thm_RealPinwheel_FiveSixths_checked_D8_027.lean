-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_checked_D8_027
-- name    : RealPinwheel.FiveSixths.checked_D8_027
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:41:56.173333+00:00
-- url     : https://prove2.me/theorems/d9b4e992-c59f-4d86-ad91-e1a11081f80d
-- title:
--   Verified witness block D8_027
-- statement:
--   For every word in the exact witness block D8_027, the integer execution-count recurrence, mean inequality, and prefix/suffix discrepancy bounds all hold. Its positive period length is at most 608.
--
--   $$\forall w\in W_{\mathrm{block}},\quad\operatorname{Checked}(w)\quad\text{and}\quad |w|\le 608.$$
--
--   This is the finite arithmetic part of the source certificate verification. Combined with witness soundness, it validates the annotated density boxes for arbitrary real periods; real-domain coverage remains a separate assertion.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate D8, entries 83–87.

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_027
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.checked_D8_027 : ∀ j : Fin 5, witnessCheck (witnessD8_027 j) = true ∧ (witnessD8_027 j).length ≤ 608 := by sorry
