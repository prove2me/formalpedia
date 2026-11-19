-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_0268
-- name    : RealPinwheel.FiveSixths.covered_fragment_P9_0268
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T06:29:32.108128+00:00
-- url     : https://prove2.me/theorems/ed9c90f0-b215-478c-bacf-65555ba8b33a
-- title:
--   Real-domain coverage fragment P9 268
-- statement:
--   Let $R_\Gamma$ be the real vectors satisfying this fragment's finite context of strict and non-strict coordinate restrictions, together with positivity, ordering, and the initial density or potential bound. These vectors are covered by the source's annotated word boxes:
--
--   $$R_\Gamma\subseteq\bigcup_{j<N} B_j.$$
--
--   Complementary coordinate cuts partition the initial domain into these regions. Separate exact arithmetic proofs establish this coverage; no rationality restriction is imposed on the real vector.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Certificate family P9; exact real-domain coverage fragment.

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.covered_fragment_P9_0268 (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((upperAtom (⟨7, by decide⟩ : Fin 9) 1 40 false) :: (complementAtom (upperAtom (⟨6, by decide⟩ : Fin 9) 1 20 false)) :: (upperAtom (⟨4, by decide⟩ : Fin 9) 1 10 false) :: (upperAtom (⟨2, by decide⟩ : Fin 9) 1 8 false) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 4 27 true)) :: (complementAtom (upperAtom (⟨5, by decide⟩ : Fin 9) 1 18 false)) :: (complementAtom (upperAtom (⟨4, by decide⟩ : Fin 9) 1 14 false)) :: (complementAtom (upperAtom (⟨3, by decide⟩ : Fin 9) 1 13 false)) :: (complementAtom (upperAtom (⟨2, by decide⟩ : Fin 9) 13 138 false)) :: (complementAtom (upperAtom (⟨1, by decide⟩ : Fin 9) 7 68 false)) :: (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by sorry
