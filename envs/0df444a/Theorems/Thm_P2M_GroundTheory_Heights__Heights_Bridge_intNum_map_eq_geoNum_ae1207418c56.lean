-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_intNum_map_eq_geoNum_ae1207418c56
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_intNum_map_eq_geoNum_ae1207418c56
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:07:19.72286+00:00
-- url     : https://prove2.me/theorems/3619c1fd-2693-4d7a-830d-97bdbbd8a7a5
-- title:
--   P2 M Ground Theory Heights  Heights Bridge int Num map eq geo Num ae1207418c56: P2 M Ground Theory Heights  Heights Bridge int Num map eq geo Num ae1207418c56
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge int Num map eq geo Num ae1207418c56 construction uses the P2 M Ground Theory Heights  Heights Bridge int Num map eq geo Num ae1207418c56 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L216-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L216-L243

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
open GeoNum

theorem P2M_GroundTheory_Heights__Heights_Bridge_intNum_map_eq_geoNum_ae1207418c56 {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (p : ℕ) [Fact p.Prime] (n : ℕ) (V : Ideal (Geo.MRing ι))
    (hV : Geo.IsMultiProjPrime V) (hpV : (C (p : ℤ) : Geo.MRing ι) ∈ V)
    (hdim : ringKrullDim (Geo.MRing ι ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞))
    (a : Fin n → K → ℤ) :
    intNum (ZMod p) (V.map (MvPolynomial.map (Int.castRingHom (ZMod p)))) a = Geo.geoNum n V a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«intNum_map_eq_geoNum» := P2M_GroundTheory_Heights__Heights_Bridge_intNum_map_eq_geoNum_ae1207418c56
