-- Prove2me | Theorems.Thm_PrivateUniformGen_Characterization_corollary_6_8
-- name    : PrivateUniformGen.Characterization.corollary_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:01:28.65696+00:00
-- url     : https://prove2.me/theorems/49d2778a-a4aa-4b7c-bfa9-1349abb1333f
-- title:
--   Corollary 6.8 — Binary rank comparison
-- statement:
--   Let $C$ be a language class over a countable space. If its finite-intersection Helly number and binary nested branching dimension are finite, then
--
--   $$\operatorname{NBDim}(C)\le2^{\operatorname{NBDim}_2(C)}-1.$$
--
--   The right side is computed using the finite binary dimension; the left side remains an extended natural number, so the bound also asserts its finiteness. The subtraction cannot truncate a negative quantity because $2^b\ge1$ for every natural $b$.
--
--   Differences from the source:
--   - encoding: CDim in {-1,0,1,...,infinity} and nonnegative ranks with infinity → WithTop integers for CDim and extended naturals for ranks and Helly numbers; reason: retains both -1 and infinity; finite-value projections are used only where finiteness is assumed or follows from the source results
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Corollary 6.8, p. 24. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Branching
import Definitions.Def_PrivateUniformGen_Characterization_Helly

open MeasureTheory

namespace PrivateUniformGen.Characterization

theorem corollary_6_8 {X : Type} [Countable X] (C : LanguageClass X)
    (hh : hellyNumber C.languages < ⊤) (hbin : nbDim C 2 < ⊤) :
  nbDim C ⊤ ≤ ((2 ^ (nbDim C 2).toNat - 1 : ℕ) : ℕ∞) := by sorry

end PrivateUniformGen.Characterization
