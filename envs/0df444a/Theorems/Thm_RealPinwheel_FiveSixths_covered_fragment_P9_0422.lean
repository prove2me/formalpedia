-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0422
-- name    : RealPinwheel.FiveSixths.covered_fragment_P9_0422
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T06:48:57.775392+00:00
-- url     : https://prove2.me/theorems/9c83fe3a-8017-4eae-b8db-467501d01e68
-- title:
--   Real-domain coverage fragment P9 422
-- statement:
--   Let $R_\Gamma$ be the real vectors satisfying this fragment's strict and non-strict coordinate restrictions, positivity, ordering, and the initial density or potential bound. The source's annotated word boxes cover this region:
--
--   $$R_\Gamma\subseteq\bigcup_{j<N}B_j.$$
--
--   The exact arithmetic proof is independent of rationality of the real vector. Complementary coordinate cuts connect these fragments to the initial domain.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate family P9; exact real-domain coverage fragment.

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.covered_fragment_P9_0422 (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((upperAtom (⟨0, by decide⟩ : Fin 9) 11 40 false) :: (upperAtom (⟨1, by decide⟩ : Fin 9) 9 40 false) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 17 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 1 4 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 1 14 false)) :: (upperAtom (⟨5, by decide⟩ : Fin 9) 1 16 true) :: (upperAtom (⟨1, by decide⟩ : Fin 9) 1 4 true) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 2 11 false)) :: (upperAtom (⟨2, by decide⟩ : Fin 9) 1 11 false) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 2 21 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 2 7 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by sorry
