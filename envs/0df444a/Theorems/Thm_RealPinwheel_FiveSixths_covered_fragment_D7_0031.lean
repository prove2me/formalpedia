-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_D7_0031
-- name    : RealPinwheel.FiveSixths.covered_fragment_D7_0031
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T06:22:13.339641+00:00
-- url     : https://prove2.me/theorems/4efa0a30-9b79-40fd-b111-31634656a07a
-- title:
--   Real-domain coverage fragment F_D7_0031
-- statement:
--   Let $R_\Gamma$ be the real density vectors satisfying this fragment's finite context of strict and non-strict coordinate restrictions, together with the initial ordering, positivity, and density or potential bound. Every such vector belongs to an annotated box of the source certificate family:
--
--   $$R_\Gamma\subseteq\bigcup_{j<N}B_j.$$
--
--   The conclusion is coverage over arbitrary real vectors. The root context has no extra coordinate restrictions and therefore covers the entire density or potential domain. Child contexts partition this domain by exact complementary coordinate inequalities.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate family D7; arithmetic validation of a fragment of the real-domain covering proof.

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD7
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.covered_fragment_D7_0031 (d : Fin 7 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨3, by decide⟩ : Fin 7) 7 120 false)) :: (upperAtom (⟨2, by decide⟩ : Fin 7) 7 60 false) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 7) 1 16 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 7) 3 13 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 7) 1 6 true)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 7) 1 10 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 7) 2 5 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 7) 3 10 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 7) 2 11 false)) :: initialAtoms 7 7 : List (LinearAtom 7)), a.Holds d) :
    ∃ j : Fin 1657, codeBox (codeFunctionD7 j.val) d := by sorry
