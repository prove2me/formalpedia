-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PsiQuadratic___nsmul_8ec651840e68
-- name    : P2M_GlobalTheory_PsiQuadratic___nsmul_8ec651840e68
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:05.39532+00:00
-- url     : https://prove2.me/theorems/626b9d65-a7b5-466f-b89c-522a63fba83e
-- title:
--   P2 M Global Theory Psi Quadratic   nsmul 8ec651840e68: P2 M Global Theory Psi Quadratic   nsmul 8ec651840e68
-- statement:
--   The P2 M Global Theory Psi Quadratic   nsmul 8ec651840e68 construction uses the P2 M Global Theory Psi Quadratic   nsmul 8ec651840e68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataPsiQuadraticGeneratorsLinear.lean#L31-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataPsiQuadraticGeneratorsLinear.lean#L31-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.PsiQuadratic
variable {O : Type} [CommRing O] (N : NumD O)

theorem P2M_GlobalTheory_PsiQuadratic___nsmul_8ec651840e68 (n : ℕ) (y : N.X) : N.ψ (n • y) * mulq N.θ N.σ n (N.c y) = N.ψ y ^ (n ^ 2) := by sorry

alias «GlobalTheory».«PsiQuadratic».«ψ_nsmul» := P2M_GlobalTheory_PsiQuadratic___nsmul_8ec651840e68
