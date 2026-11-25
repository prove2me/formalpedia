-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_quotEquiv_mk_72962265258b
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_quotEquiv_mk_72962265258b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:48:01.490934+00:00
-- url     : https://prove2.me/theorems/e383fd8e-0c6d-52db-945a-5a0fdcccb9b2
-- title:
--   P2 M Ground Theory Heights  Heights Bridge Geo Num quot Equiv mk 72962265258b: P2 M Ground Theory Heights  Heights Bridge Geo Num quot Equiv mk 72962265258b
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge Geo Num quot Equiv mk 72962265258b construction uses the P2 M Ground Theory Heights  Heights Bridge Geo Num quot Equiv mk 72962265258b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L53-L55

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

theorem P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_quotEquiv_mk_72962265258b (J' : Ideal (MRing ι (ZMod p))) (x : MRing ι ℤ) :
    quotEquiv p J' (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk J' (red p x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«GeoNum».«quotEquiv_mk» := P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_quotEquiv_mk_72962265258b
