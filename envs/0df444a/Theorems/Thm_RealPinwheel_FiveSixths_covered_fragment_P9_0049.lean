-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0049
-- name    : RealPinwheel.FiveSixths.covered_fragment_P9_0049
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:23:36.190672+00:00
-- url     : https://prove2.me/theorems/b3b1e1ee-0d84-4477-8dcc-bfe0112976ca
-- title:
--   Real-domain coverage fragment F_P9_0049
-- statement:
--   Let $R_\Gamma$ be the real density vectors satisfying this fragment's finite context of strict and non-strict coordinate restrictions, together with the initial ordering, positivity, and density or potential bound. Every such vector belongs to an annotated box of the source certificate family:
--
--   $$R_\Gamma\subseteq\bigcup_{j<N}B_j.$$
--
--   The conclusion is coverage over arbitrary real vectors. The root context has no extra coordinate restrictions and therefore covers the entire density or potential domain. Child contexts partition this domain by exact complementary coordinate inequalities.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate family P9; arithmetic validation of a fragment of the real-domain covering proof.

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.covered_fragment_P9_0049 (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 5 29 false)) :: (upperAtom (⟨4, by decide⟩ : Fin 9) 2 15 true) :: (upperAtom (⟨2, by decide⟩ : Fin 9) 1 6 true) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 1 6 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 10 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 5 36 false)) :: (upperAtom (⟨5, by decide⟩ : Fin 9) 1 18 false) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 14 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 1 13 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 13 138 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 7 68 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by sorry
