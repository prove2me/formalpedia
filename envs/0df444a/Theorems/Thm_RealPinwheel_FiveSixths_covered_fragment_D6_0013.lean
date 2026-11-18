-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D6_0013
-- name    : RealPinwheel.FiveSixths.covered_fragment_D6_0013
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:25:52.671409+00:00
-- url     : https://prove2.me/theorems/59e4b430-91f8-4cf4-a25e-98235a746a3d
-- title:
--   Real-domain coverage fragment F_D6_0013
-- statement:
--   Let $R_\Gamma$ be the real density vectors satisfying this fragment's finite context of strict and non-strict coordinate restrictions, together with the initial ordering, positivity, and density or potential bound. Every such vector belongs to an annotated box of the source certificate family:
--
--   $$R_\Gamma\subseteq\bigcup_{j<N}B_j.$$
--
--   The conclusion is coverage over arbitrary real vectors. The root context has no extra coordinate restrictions and therefore covers the entire density or potential domain. Child contexts partition this domain by exact complementary coordinate inequalities.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate family D6; arithmetic validation of a fragment of the real-domain covering proof.

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD6
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.covered_fragment_D6_0013 (d : Fin 6 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨1, by decide⟩ : Fin 6) 2 13 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 6) 2 21 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 6) 4 9 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 6) 1 3 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 6) 2 11 false)) :: initialAtoms 6 6 : List (LinearAtom 6)), a.Holds d) :
    ∃ j : Fin 630, codeBox (codeFunctionD6 j.val) d := by sorry
