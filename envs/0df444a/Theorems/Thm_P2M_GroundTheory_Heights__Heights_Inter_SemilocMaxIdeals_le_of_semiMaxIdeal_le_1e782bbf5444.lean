-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_le_of_semiMaxIdeal_le_1e782bbf5444
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_le_of_semiMaxIdeal_le_1e782bbf5444
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:44:07.378539+00:00
-- url     : https://prove2.me/theorems/a2653d20-b77c-49c6-b1fa-efcdb8c48879
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals le of semi Max Ideal le 1e782bbf5444: P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals le of semi Max Ideal le 1e782bbf5444
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals le of semi Max Ideal le 1e782bbf5444 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals le of semi Max Ideal le 1e782bbf5444 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocMaxIdeals.lean#L103-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocMaxIdeals.lean#L103-L121

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_le_of_semiMaxIdeal_le_1e782bbf5444 (hfin : 𝒲.Finite) (h𝒲 : ∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W)
    {W₁ W₂ : Ideal (MRing ι)} (h₁ : W₁ ∈ 𝒲) (h₂ : W₂ ∈ 𝒲) [IsLocalRing (locRing P W₁)]
    [IsLocalRing (locRing P W₂)] (hle : semiMaxIdeal P 𝒲 W₁ h₁ ≤ semiMaxIdeal P 𝒲 W₂ h₂) : W₁ ≤ W₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocMaxIdeals».«le_of_semiMaxIdeal_le» := P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_le_of_semiMaxIdeal_le_1e782bbf5444
