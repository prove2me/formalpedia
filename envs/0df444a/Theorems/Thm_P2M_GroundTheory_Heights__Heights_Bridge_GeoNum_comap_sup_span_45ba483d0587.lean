-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_comap_sup_span_45ba483d0587
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_comap_sup_span_45ba483d0587
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:09:30.715128+00:00
-- url     : https://prove2.me/theorems/8b31feed-ad44-42d1-ab34-6f51e9c5cdfc
-- title:
--   P2 M Ground Theory Heights  Heights Bridge Geo Num comap sup span 45ba483d0587: P2 M Ground Theory Heights  Heights Bridge Geo Num comap sup span 45ba483d0587
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge Geo Num comap sup span 45ba483d0587 construction uses the P2 M Ground Theory Heights  Heights Bridge Geo Num comap sup span 45ba483d0587 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L37-L41

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

theorem P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_comap_sup_span_45ba483d0587 (Q : Ideal (MRing ι (ZMod p))) (T : Set (MRing ι ℤ)) :
    Q.comap (red p) ⊔ Ideal.span T = (Q ⊔ Ideal.span (red p '' T)).comap (red p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«GeoNum».«comap_sup_span» := P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_comap_sup_span_45ba483d0587
