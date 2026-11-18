-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D6_0014
-- name    : RealPinwheel.FiveSixths.covered_fragment_D6_0014
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:51:36.29878+00:00
-- url     : https://prove2.me/theorems/ab47ed89-27ce-4e31-814c-c5ed2002ce55
-- title:
--   Real-domain coverage of certificate D6
-- statement:
--   Every positive antitone real density vector satisfying the initial density or potential bound belongs to an annotated box of the source certificate family:
--
--   $$R_{\mathrm{initial}}\subseteq\bigcup_{j<N}B_j.$$
--
--   This is the root real-domain coverage assertion. Its companion word-validity lemmas supply all-window valid periodic schedules inside each annotated box.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Root coverage assertion for family D6.

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD6
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.covered_fragment_D6_0014 (d : Fin 6 → ℝ) (hΓ : ∀ a ∈ (initialAtoms 6 6 : List (LinearAtom 6)), a.Holds d) :
    ∃ j : Fin 630, codeBox (codeFunctionD6 j.val) d := by sorry
