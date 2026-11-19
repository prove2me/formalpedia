-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_1355
-- name    : RealPinwheel.FiveSixths.covered_fragment_P9_1355
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:53:58.510195+00:00
-- url     : https://prove2.me/theorems/f385e8dd-9f18-46c3-85f7-31fa7a408e64
-- title:
--   Real-domain coverage fragment P9 1355
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

theorem RealPinwheel.FiveSixths.covered_fragment_P9_1355 (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((upperAtom (⟨1, by decide⟩ : Fin 9) 1 8 false) :: (upperAtom (⟨7, by decide⟩ : Fin 9) 1 32 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 9 22 false)) :: (upperAtom (⟨4, by decide⟩ : Fin 9) 1 22 false) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 1 21 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 2 27 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 9) 4 27 false) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 2 27 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 4 9 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 5 13 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 2 7 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by sorry
