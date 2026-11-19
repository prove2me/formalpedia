-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0980
-- name    : RealPinwheel.FiveSixths.covered_fragment_P9_0980
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T09:13:19.877312+00:00
-- url     : https://prove2.me/theorems/b9b57e7c-1300-4f3c-b85c-4ea5c51ee868
-- title:
--   Real-domain coverage fragment P9 980
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

theorem RealPinwheel.FiveSixths.covered_fragment_P9_0980 (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((upperAtom (⟨6, by decide⟩ : Fin 9) 1 40 false) :: (complementAtom (upperAtom (⟨5, by decide⟩ : Fin 9) 3 80 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 7 30 false) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 14 true)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 5 24 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 24 false)) :: (upperAtom (⟨2, by decide⟩ : Fin 9) 1 6 true) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 3 16 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 1 15 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 23 168 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 1 11 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 2 21 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 2 7 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by sorry
