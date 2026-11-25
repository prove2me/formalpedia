-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_imageVar_eq_comap_33f58e435336
-- name    : P2M_GroundTheory_Heights__Heights_Targets_imageVar_eq_comap_33f58e435336
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:16.605803+00:00
-- url     : https://prove2.me/theorems/52f3ae91-c273-559a-a809-fd03ca3abce2
-- title:
--   P2 M Ground Theory Heights  Heights Targets image Var eq comap 33f58e435336: P2 M Ground Theory Heights  Heights Targets image Var eq comap 33f58e435336
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets image Var eq comap 33f58e435336 construction uses the P2 M Ground Theory Heights  Heights Targets image Var eq comap 33f58e435336 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjDeg.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjDeg.lean#L43-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumRatSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsFnDegRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers
noncomputable section
universe u
variable {K K' : Type} {ι : K → Type} {ι' : K' → Type} {κ : K → K'}
  {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem P2M_GroundTheory_Heights__Heights_Targets_imageVar_eq_comap_33f58e435336 {F : Type u} [Field F] (hb : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v)
    (V' : Ideal (MRing ι' F)) :
    ReciprocityTheory.ChartRestriction.G.AI.I1.imageVar F v V' =
      (contractPrime ⟨κ, hb.1⟩ V').comap (rename (blockVarEquiv hb)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«imageVar_eq_comap» := P2M_GroundTheory_Heights__Heights_Targets_imageVar_eq_comap_33f58e435336
