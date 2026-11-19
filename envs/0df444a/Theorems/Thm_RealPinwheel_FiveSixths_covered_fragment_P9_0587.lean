-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0587
-- name    : RealPinwheel.FiveSixths.covered_fragment_P9_0587
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T07:27:46.308045+00:00
-- url     : https://prove2.me/theorems/a842b0d6-2877-4beb-99c6-2effeaa80a29
-- title:
--   Real-domain coverage fragment P9 587
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

theorem RealPinwheel.FiveSixths.covered_fragment_P9_0587 (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 1 7 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 1 4 true) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 13 108 false)) :: (upperAtom (⟨3, by decide⟩ : Fin 9) 13 144 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 4 17 false)) :: (complementAtom (upperAtom (⟨7, by decide⟩ : Fin 9) 1 30 false)) :: (complementAtom (upperAtom (⟨6, by decide⟩ : Fin 9) 1 20 false)) :: (complementAtom (upperAtom (⟨5, by decide⟩ : Fin 9) 9 152 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 18 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 9) 1 6 true) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 23 336 false)) :: (upperAtom (⟨2, by decide⟩ : Fin 9) 23 168 false) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 1 11 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 2 21 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 2 7 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by sorry
