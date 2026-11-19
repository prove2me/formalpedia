-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_covered_fragment_P9_1440
-- name    : RealPinwheel.FiveSixths.covered_fragment_P9_1440
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T06:42:59.705044+00:00
-- url     : https://prove2.me/theorems/b6c7e737-d8ce-40df-955d-8f97ae922652
-- title:
--   Real-domain coverage supporting the nine-task root
-- statement:
--   The real density vectors satisfying this finite context are contained in the union of the annotated source boxes:
--
--   $$R_\Gamma\subseteq\bigcup_{j<N}B_j.$$
--
--   This region is one of the direct subregions in the source's nine-task potential-domain verification. Strict coordinate restrictions are retained, and the vector is not assumed rational.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Direct subregion of the root potential-domain coverage certificate.

import Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.covered_fragment_P9_1440 (d : Fin 9 → ℝ) (hΓ : ∀ a ∈ ((complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 2 7 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 7 34 false)) :: (complementAtom (upperAtom (⟨0, by decide⟩ : Fin 9) 11 96 false)) :: initialAtoms 9 8 : List (LinearAtom 9)), a.Holds d) :
    ∃ j : Fin 7968, codeBox (codeFunctionP9 j.val) d := by sorry
