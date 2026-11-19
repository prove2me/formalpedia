-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D8_0104
-- name    : RealPinwheel.FiveSixths.covered_fragment_D8_0104
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T07:35:33.216684+00:00
-- url     : https://prove2.me/theorems/8f3fb157-6a0c-43b5-86f3-23c51fd4196c
-- title:
--   Real-domain coverage fragment F_D8_0104
-- statement:
--   Let $R_\Gamma$ be the real density vectors satisfying this fragment's finite context of strict and non-strict coordinate restrictions, together with the initial ordering, positivity, and density or potential bound. Every such vector belongs to an annotated box of the source certificate family:
--
--    $$R_\Gamma\subseteq\bigcup_{j<N}B_j.$$
--
--    The conclusion is coverage over arbitrary real vectors. The root context has no extra coordinate restrictions and therefore covers the entire density or potential domain. Child contexts partition this domain by exact complementary coordinate inequalities.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate family D8; arithmetic validation of a fragment of the real-domain covering proof.

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.covered_fragment_D8_0104 (d : Fin 8 → ℝ) (hΓ : ∀ a ∈ ((upperAtom (⟨6, by decide⟩ : Fin 8) 5 84 false) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 8) 1 10 true)) :: (complementAtom (upperAtom (⟨6, by decide⟩ : Fin 8) 7 144 false)) :: (upperAtom (⟨4, by decide⟩ : Fin 8) 7 72 false) :: (upperAtom (⟨0, by decide⟩ : Fin 8) 7 24 false) :: (complementAtom (upperAtom (⟨5, by decide⟩ : Fin 8) 1 17 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 8) 1 16 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 8) 3 16 false) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 8) 1 15 false)) :: (upperAtom (⟨2, by decide⟩ : Fin 8) 2 15 false) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 8) 2 27 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 1 8 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 8) 1 3 true) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 1 4 true)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 2 15 false)) :: initialAtoms 8 8 : List (LinearAtom 8)), a.Holds d) :
    ∃ j : Fin 3725, codeBox (codeFunctionD8 j.val) d := by sorry
