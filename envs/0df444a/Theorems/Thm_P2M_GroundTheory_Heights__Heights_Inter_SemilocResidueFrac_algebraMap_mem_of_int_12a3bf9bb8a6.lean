-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_algebraMap_mem_of_int_12a3bf9bb8a6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_algebraMap_mem_of_int_12a3bf9bb8a6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:51:30.997574+00:00
-- url     : https://prove2.me/theorems/66c84e76-cac6-5dc6-8903-95d543cc0aab
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac algebra Map mem of int 12a3bf9bb8a6: P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac algebra Map mem of int 12a3bf9bb8a6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac algebra Map mem of int 12a3bf9bb8a6 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac algebra Map mem of int 12a3bf9bb8a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L136-L140

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocResidueFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocResidueFrac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocResidueFrac
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_algebraMap_mem_of_int_12a3bf9bb8a6 {F : Type} [Field F] [Algebra F Ω] (hF : ∀ c : F, ∃ a b : ℤ, (b : F) ≠ 0 ∧ c = a / b)
    (S : Subfield Ω) (c : F) : algebraMap F Ω c ∈ S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocResidueFrac».«algebraMap_mem_of_int» := P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_algebraMap_mem_of_int_12a3bf9bb8a6
