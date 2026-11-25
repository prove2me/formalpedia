-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_IntersectionWithSection_comp_mem_mcPts_4a4d6fbde8a7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_IntersectionWithSection_comp_mem_mcPts_4a4d6fbde8a7
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:33:03.255294+00:00
-- url     : https://prove2.me/theorems/9d7dd71f-cb09-4a48-b239-27bd9074719a
-- title:
--   P2 M Ground Theory Heights  Heights Inter Intersection With Section comp mem mc Pts 4a4d6fbde8a7: P2 M Ground Theory Heights  Heights Inter Intersection With Section comp mem mc Pts 4a4d6fbde8a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Intersection With Section comp mem mc Pts 4a4d6fbde8a7 construction uses the P2 M Ground Theory Heights  Heights Inter Intersection With Section comp mem mc Pts 4a4d6fbde8a7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PullWMemFibre.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PullWMemFibre.lean#L22-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedE
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsIntegralLogNormRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
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
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Inter.IntersectionWithSection
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_IntersectionWithSection_comp_mem_mcPts_4a4d6fbde8a7 {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} {z' : (Σ k', ι' k') → ℂ} (hz : z' ∈ mcPts P') :
    (fun p => z' (v p)) ∈ mcPts (imageZ v P') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«IntersectionWithSection».«comp_mem_mcPts» := P2M_GroundTheory_Heights__Heights_Inter_IntersectionWithSection_comp_mem_mcPts_4a4d6fbde8a7
