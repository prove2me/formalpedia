-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PsiQuadratic___self_27515abbac20
-- name    : P2M_GlobalTheory_PsiQuadratic___self_27515abbac20
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:08.889322+00:00
-- url     : https://prove2.me/theorems/2aae8e22-50aa-4e48-9e2e-65ed344fb12a
-- title:
--   P2 M Global Theory Psi Quadratic   self 27515abbac20: P2 M Global Theory Psi Quadratic   self 27515abbac20
-- statement:
--   The P2 M Global Theory Psi Quadratic   self 27515abbac20 construction uses the P2 M Global Theory Psi Quadratic   self 27515abbac20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataPsiQuadraticGeneratorsLinear.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/DegenerationDataPsiQuadraticGeneratorsLinear.lean#L9-L19

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

theorem P2M_GlobalTheory_PsiQuadratic___self_27515abbac20 (y : N.X) : N.τ y y = N.ψ y ^ 2 * dbl N.θ N.σ (N.c y) := by sorry

alias «GlobalTheory».«PsiQuadratic».«τ_self» := P2M_GlobalTheory_PsiQuadratic___self_27515abbac20
