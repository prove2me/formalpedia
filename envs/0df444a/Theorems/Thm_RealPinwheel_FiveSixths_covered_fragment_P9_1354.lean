-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_1354
-- name    : RealPinwheel.FiveSixths.covered_fragment_P9_1354
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:54:10.499204+00:00
-- url     : https://prove2.me/theorems/340c4aa9-b43c-4463-9afd-4ac7d86450c9
-- title:
--   Real-domain coverage fragment P9 1354
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

theorem RealPinwheel.FiveSixths.covered_fragment_P9_1354 (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 18 false)) :: (upperAtom (⟨2, by decide⟩ : Fin 9) 2 27 false) :: (upperAtom (⟨1, by decide⟩ : Fin 9) 4 27 false) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 2 27 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 4 9 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 5 13 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 2 7 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by sorry
