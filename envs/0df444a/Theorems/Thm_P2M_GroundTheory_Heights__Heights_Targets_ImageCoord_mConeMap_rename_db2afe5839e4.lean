-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ImageCoord_mConeMap_rename_db2afe5839e4
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ImageCoord_mConeMap_rename_db2afe5839e4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:49.270954+00:00
-- url     : https://prove2.me/theorems/7b36e363-d7ef-4cdd-aae2-a9c54b93a3be
-- title:
--   P2 M Ground Theory Heights  Heights Targets Image Coord m Cone Map rename db2afe5839e4: P2 M Ground Theory Heights  Heights Targets Image Coord m Cone Map rename db2afe5839e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Image Coord m Cone Map rename db2afe5839e4 construction uses the P2 M Ground Theory Heights  Heights Targets Image Coord m Cone Map rename db2afe5839e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ImageCoord.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ImageCoord.lean#L11-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ImageCoord
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem P2M_GroundTheory_Heights__Heights_Targets_ImageCoord_mConeMap_rename_db2afe5839e4 {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (hv : ∀ p, (v p).1 = κ p.1)
    {Ω : Type} [Field Ω] (y : (Σ k', ι' k') → Ω) (f : MRing ι) :
    mConeMap y (rename v f) = rename κ (mConeMap (y ∘ v) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ImageCoord».«mConeMap_rename» := P2M_GroundTheory_Heights__Heights_Targets_ImageCoord_mConeMap_rename_db2afe5839e4
