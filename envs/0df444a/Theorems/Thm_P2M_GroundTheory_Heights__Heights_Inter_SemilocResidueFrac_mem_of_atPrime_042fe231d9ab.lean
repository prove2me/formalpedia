-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_mem_of_atPrime_042fe231d9ab
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_mem_of_atPrime_042fe231d9ab
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:46:31.581843+00:00
-- url     : https://prove2.me/theorems/91444b82-df36-4378-9a41-e537e5bc9bd7
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac mem of at Prime 042fe231d9ab: P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac mem of at Prime 042fe231d9ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac mem of at Prime 042fe231d9ab construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Residue Frac mem of at Prime 042fe231d9ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L142-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocResidueFrac.lean#L142-L150

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_mem_of_atPrime_042fe231d9ab {B C : Type*} [CommRing B] [CommRing C] [Algebra B C] (𝔪 : Ideal B) [𝔪.IsPrime]
    [IsLocalization.AtPrime C 𝔪] (ρ : C →+* Ω) (hker : ∀ b, ρ (algebraMap B C b) = 0 ↔ b ∈ 𝔪) (S : Subfield Ω)
    (hS : ∀ b, ρ (algebraMap B C b) ∈ S) (z : C) : ρ z ∈ S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocResidueFrac».«mem_of_atPrime» := P2M_GroundTheory_Heights__Heights_Inter_SemilocResidueFrac_mem_of_atPrime_042fe231d9ab
