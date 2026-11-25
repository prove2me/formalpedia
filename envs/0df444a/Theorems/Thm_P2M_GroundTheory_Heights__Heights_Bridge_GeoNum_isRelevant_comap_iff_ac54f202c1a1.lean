-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_isRelevant_comap_iff_ac54f202c1a1
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_isRelevant_comap_iff_ac54f202c1a1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:57:56.143801+00:00
-- url     : https://prove2.me/theorems/f1c67f86-70be-4ea1-9a8e-8fe699456189
-- title:
--   P2 M Ground Theory Heights  Heights Bridge Geo Num is Relevant comap iff ac54f202c1a1: P2 M Ground Theory Heights  Heights Bridge Geo Num is Relevant comap iff ac54f202c1a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge Geo Num is Relevant comap iff ac54f202c1a1 construction uses the P2 M Ground Theory Heights  Heights Bridge Geo Num is Relevant comap iff ac54f202c1a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L43-L45

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

theorem P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_isRelevant_comap_iff_ac54f202c1a1 (Q : Ideal (MRing ι (ZMod p))) :
    Geo.IsRelevant (R := ℤ) (Q.comap (red p)) ↔ IsRelevant Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«GeoNum».«isRelevant_comap_iff» := P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_isRelevant_comap_iff_ac54f202c1a1
