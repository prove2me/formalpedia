-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_scale_b69a487db7c3
-- name    : P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_scale_b69a487db7c3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:33:44.854412+00:00
-- url     : https://prove2.me/theorems/1672eb9e-fbf2-4e03-89a4-be8c0fd81510
-- title:
--   P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals exists scale b69a487db7c3: P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals exists scale b69a487db7c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals exists scale b69a487db7c3 construction uses the P2 M Ground Theory Heights  Heights Inter Semiloc Max Ideals exists scale b69a487db7c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocMaxIdeals.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PSemilocMaxIdeals.lean#L93-L99

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

theorem P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_scale_b69a487db7c3 (hfin : 𝒲.Finite) (h𝒲 : ∀ W ∈ 𝒲, IsMultiProjPrime W) (a : K → ℕ) {W' : Ideal (MRing ι)}
    (hr : IsRelevant W') (hp : W'.IsPrime) :
    ∃ (t h : MRing ι) (d : K → ℕ), IsMultiHomog t d ∧ IsMultiHomog h (a + d) ∧ t ∉ W' ∧ ∀ W ∈ 𝒲, h ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«SemilocMaxIdeals».«exists_scale» := P2M_GroundTheory_Heights__Heights_Inter_SemilocMaxIdeals_exists_scale_b69a487db7c3
