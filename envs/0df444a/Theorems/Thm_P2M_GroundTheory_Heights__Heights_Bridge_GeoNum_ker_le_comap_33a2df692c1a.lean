-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_ker_le_comap_33a2df692c1a
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_ker_le_comap_33a2df692c1a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:33.073794+00:00
-- url     : https://prove2.me/theorems/3bee4b81-9023-41fe-ad9f-d373f197a937
-- title:
--   P2 M Ground Theory Heights  Heights Bridge Geo Num ker le comap 33a2df692c1a: P2 M Ground Theory Heights  Heights Bridge Geo Num ker le comap 33a2df692c1a
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge Geo Num ker le comap 33a2df692c1a construction uses the P2 M Ground Theory Heights  Heights Bridge Geo Num ker le comap 33a2df692c1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L27-L30

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

theorem P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_ker_le_comap_33a2df692c1a (J' : Ideal (MRing ι (ZMod p))) :
    RingHom.ker (red (ι := ι) p) ≤ J'.comap (red p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«GeoNum».«ker_le_comap» := P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_ker_le_comap_33a2df692c1a
