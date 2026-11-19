-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_1138
-- name    : RealPinwheel.FiveSixths.covered_fragment_P9_1138
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:56:22.435978+00:00
-- url     : https://prove2.me/theorems/22782d26-0ebf-43d0-a154-7d895b2db029
-- title:
--   Real-domain coverage fragment P9 1138
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

theorem RealPinwheel.FiveSixths.covered_fragment_P9_1138 (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨7, by decide⟩ : Fin 9) 1 40 true)) :: (upperAtom (⟨5, by decide⟩ : Fin 9) 1 15 false) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 2 21 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 1 3 true) :: (complementAtom (upperAtom (⟨6, by decide⟩ : Fin 9) 1 42 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 1 10 true)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 16 51 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 1 9 false)) :: (complementAtom (upperAtom (⟨5, by decide⟩ : Fin 9) 1 24 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 18 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 1 15 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 5 64 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 9) 5 32 false) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 1 13 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 5 13 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 2 7 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by sorry
