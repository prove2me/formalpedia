-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_eq_of_isMaximal_8f112829d4e5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_eq_of_isMaximal_8f112829d4e5
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:24:41.592904+00:00
-- url     : https://prove2.me/theorems/1f77e50d-50ee-48f2-9ab9-1a10d7010248
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals exists eq of is Maximal 8f112829d4e5: P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals exists eq of is Maximal 8f112829d4e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals exists eq of is Maximal 8f112829d4e5 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals exists eq of is Maximal 8f112829d4e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocMaxIdeals.lean#L154-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocMaxIdeals.lean#L154-L181

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocMaxIdeals
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
open GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals
open regularityLocalFlat_holds
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  (P : Ideal (MRing ι)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι)))
variable {P 𝒲}

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_eq_of_isMaximal_8f112829d4e5 (hfin : 𝒲.Finite) (h𝒲 : ∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W)
    (hne : 𝒲.Nonempty) (M : Ideal (semiLocRing P 𝒲)) (hM : M.IsMaximal) :
    ∃ (W' : Ideal (MRing ι)) (hW' : W' ∈ 𝒲), ∀ [IsLocalRing (locRing P W')], M = semiMaxIdeal P 𝒲 W' hW' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocMaxIdeals».«exists_eq_of_isMaximal» := P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_eq_of_isMaximal_8f112829d4e5
