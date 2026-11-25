-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_intNum_eq_geoNum_comap_82f1196bd47b
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_intNum_eq_geoNum_comap_82f1196bd47b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:49:49.922423+00:00
-- url     : https://prove2.me/theorems/666403ab-c890-512d-9282-7a2187e9bb25
-- title:
--   P2 M Ground Theory Heights  Heights Bridge Geo Num int Num eq geo Num comap 82f1196bd47b: P2 M Ground Theory Heights  Heights Bridge Geo Num int Num eq geo Num comap 82f1196bd47b
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge Geo Num int Num eq geo Num comap 82f1196bd47b construction uses the P2 M Ground Theory Heights  Heights Bridge Geo Num int Num eq geo Num comap 82f1196bd47b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L124-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L124-L210

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

theorem P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_intNum_eq_geoNum_comap_82f1196bd47b (n : ℕ) : ∀ Q : Ideal (MRing ι (ZMod p)), IsMultiProjPrime Q →
    relDim Q = ((n : ℕ) : WithBot (WithTop ℤ)) → ∀ a : Fin n → K → ℤ,
      intNum (ZMod p) Q a = Geo.geoNum n (Q.comap (red p)) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«GeoNum».«intNum_eq_geoNum_comap» := P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_intNum_eq_geoNum_comap_82f1196bd47b
