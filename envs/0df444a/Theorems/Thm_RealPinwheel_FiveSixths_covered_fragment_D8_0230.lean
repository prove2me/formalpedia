-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D8_0230
-- name    : RealPinwheel.FiveSixths.covered_fragment_D8_0230
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:55:50.571493+00:00
-- url     : https://prove2.me/theorems/d81b116b-88fe-474b-b34a-7c102d66a661
-- title:
--   Real-domain coverage fragment D8 230
-- statement:
--   Let $R_\Gamma$ be the real vectors satisfying this fragment's strict and non-strict coordinate restrictions, positivity, ordering, and the initial density or potential bound. The source's annotated word boxes cover this region:
--
--   $$R_\Gamma\subseteq\bigcup_{j<N}B_j.$$
--
--   The exact arithmetic proof is independent of rationality of the real vector. Complementary coordinate cuts connect these fragments to the initial domain.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate family D8; exact real-domain coverage fragment.

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.covered_fragment_D8_0230 (d : Fin 8 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨3, by decide⟩ : Fin 8) 1 15 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 8) 1 11 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 8) 1 25 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 8) 1 20 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 8) 1 5 false) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 1 7 true)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 3 40 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 8) 1 2 true) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 3 7 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 1 3 true)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 1 4 true)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 2 15 false)) :: initialAtoms 8 8 : List (LinearAtom 8)), a.Holds d) :
    ∃ j : Fin 3725, codeBox (codeFunctionD8 j.val) d := by sorry
