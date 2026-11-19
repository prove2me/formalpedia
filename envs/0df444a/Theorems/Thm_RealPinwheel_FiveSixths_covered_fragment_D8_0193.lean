-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D8_0193
-- name    : RealPinwheel.FiveSixths.covered_fragment_D8_0193
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T08:44:25.251959+00:00
-- url     : https://prove2.me/theorems/d5d6a1ba-d395-4b60-868c-b6ecc44b97e8
-- title:
--   Real-domain coverage fragment D8 193
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

theorem RealPinwheel.FiveSixths.covered_fragment_D8_0193 (d : Fin 8 → ℝ) (hΓ : ∀ a ∈ ((upperAtom (⟨0, by decide⟩ : Fin 8) 7 19 false) :: (upperAtom (⟨3, by decide⟩ : Fin 8) 3 38 false) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 8) 1 24 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 8) 1 18 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 8) 2 17 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 8) 3 17 false) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 2 15 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 8) 3 44 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 3 35 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 8) 3 7 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 1 3 true)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 1 4 true)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 2 15 false)) :: initialAtoms 8 8 : List (LinearAtom 8)), a.Holds d) :
    ∃ j : Fin 3725, codeBox (codeFunctionD8 j.val) d := by sorry
