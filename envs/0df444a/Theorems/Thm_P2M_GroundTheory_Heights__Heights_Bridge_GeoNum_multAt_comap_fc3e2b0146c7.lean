-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_multAt_comap_fc3e2b0146c7
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_multAt_comap_fc3e2b0146c7
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:18.541188+00:00
-- url     : https://prove2.me/theorems/c5305333-6c69-4ed5-bb73-d1909e77b755
-- title:
--   P2 M Ground Theory Heights  Heights Bridge Geo Num mult At comap fc3e2b0146c7: P2 M Ground Theory Heights  Heights Bridge Geo Num mult At comap fc3e2b0146c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge Geo Num mult At comap fc3e2b0146c7 construction uses the P2 M Ground Theory Heights  Heights Bridge Geo Num mult At comap fc3e2b0146c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L57-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.Bridge.GeoNum
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (p : ℕ) [Fact p.Prime]

theorem P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_multAt_comap_fc3e2b0146c7 (J' W' : Ideal (MRing ι (ZMod p))) [W'.IsPrime] :
    NumbersDVR.multAt (J'.comap (red p)) (W'.comap (red p)) = NumbersDVR.multAt J' W' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«GeoNum».«multAt_comap» := P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_multAt_comap_fc3e2b0146c7
