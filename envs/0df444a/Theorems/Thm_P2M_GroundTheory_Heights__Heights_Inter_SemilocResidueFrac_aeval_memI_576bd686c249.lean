-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_aeval_memI_576bd686c249
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_aeval_memI_576bd686c249
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:48:36.427968+00:00
-- url     : https://prove2.me/theorems/0500ac41-1a5f-4ae1-9fe3-52aa9350679e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac aeval mem I 576bd686c249: P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac aeval mem I 576bd686c249
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac aeval mem I 576bd686c249 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac aeval mem I 576bd686c249 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L102-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L102-L113

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_aeval_memI_576bd686c249 {F : Type} [Field F] [Algebra F Ω] (L : IntermediateField F Ω) {y : (Σ k, ι k) → Ω}
    (hy : ∀ p, y p ∈ L) (u : MRing ι) : aeval y u ∈ L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocResidueFrac».«aeval_memI» := P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_aeval_memI_576bd686c249
