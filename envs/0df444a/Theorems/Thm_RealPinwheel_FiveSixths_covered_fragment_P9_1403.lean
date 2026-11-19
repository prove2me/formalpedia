-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_1403
-- name    : RealPinwheel.FiveSixths.covered_fragment_P9_1403
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:06:56.421824+00:00
-- url     : https://prove2.me/theorems/13146b5b-fab3-4191-8bbb-1d0ef4b3321b
-- title:
--   Real-domain coverage fragment P9 1403
-- statement:
--   Every real density vector satisfying this exact coordinate context lies in an annotated box of the source certificate family:
--
--   $$R_\Gamma\subseteq\bigcup_{j<N}B_j.$$
--
--   The context retains positivity, ordering, the initial density or potential bound, and the complementary coordinate cuts defining this subregion. No rationality restriction is imposed.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Exact real-domain coverage fragment in certificate family P9.

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.covered_fragment_P9_1403 (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 3 46 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 9) 5 23 false) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 4 27 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 2 27 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 4 9 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 5 13 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 2 7 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by sorry
