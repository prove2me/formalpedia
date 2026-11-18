-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D8_0027
-- name    : RealPinwheel.FiveSixths.covered_fragment_D8_0027
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:35:06.860283+00:00
-- url     : https://prove2.me/theorems/c880d7a7-594d-4798-a956-6f49e4f83aa8
-- title:
--   Real-domain coverage fragment F_D8_0027
-- statement:
--   Let $R_\Gamma$ be the real density vectors satisfying this fragment's finite context of strict and non-strict coordinate restrictions, together with the initial ordering, positivity, and density or potential bound. Every such vector belongs to an annotated box of the source certificate family:
--
--   $$R_\Gamma\subseteq\bigcup_{j<N}B_j.$$
--
--   The conclusion is coverage over arbitrary real vectors. The root context has no extra coordinate restrictions and therefore covers the entire density or potential domain. Child contexts partition this domain by exact complementary coordinate inequalities.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate family D8; arithmetic validation of a fragment of the real-domain covering proof.

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.covered_fragment_D8_0027 (d : Fin 8 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 3 17 false)) :: (complementAtom (upperAtom (⟨6, by decide⟩ : Fin 8) 1 32 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 8) 3 32 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 5 32 false)) :: (complementAtom (upperAtom (⟨5, by decide⟩ : Fin 8) 1 24 false)) :: (upperAtom (⟨1, by decide⟩ : Fin 8) 3 16 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 3 16 false)) :: (upperAtom (⟨5, by decide⟩ : Fin 8) 1 16 false) :: (upperAtom (⟨3, by decide⟩ : Fin 8) 1 8 true) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 8) 7 102 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 8) 1 12 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 8) 7 60 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 8) 1 8 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 8) 1 4 true) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 8) 2 15 false)) :: initialAtoms 8 8 : List (LinearAtom 8)), a.Holds d) :
    ∃ j : Fin 3725, codeBox (codeFunctionD8 j.val) d := by sorry
