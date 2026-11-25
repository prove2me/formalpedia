-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_length_toNat_comap_27d389fba1df
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_length_toNat_comap_27d389fba1df
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:38:48.843355+00:00
-- url     : https://prove2.me/theorems/2fa79c2c-a367-474a-88d0-939a85ca9f75
-- title:
--   P2 M Ground Theory Heights  Heights Bridge Geo Num length to Nat comap 27d389fba1df: P2 M Ground Theory Heights  Heights Bridge Geo Num length to Nat comap 27d389fba1df
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge Geo Num length to Nat comap 27d389fba1df construction uses the P2 M Ground Theory Heights  Heights Bridge Geo Num length to Nat comap 27d389fba1df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L67-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L67-L78

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

theorem P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_length_toNat_comap_27d389fba1df (J' : Ideal (MRing ι (ZMod p))) :
    (Module.length ℤ (MRing ι ℤ ⧸ J'.comap (red p))).toNat =
      Module.finrank (ZMod p) (MRing ι (ZMod p) ⧸ J') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«GeoNum».«length_toNat_comap» := P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_length_toNat_comap_27d389fba1df
