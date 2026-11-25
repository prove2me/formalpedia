-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityOrder_order_of_integral_a91448df245e
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityOrder_order_of_integral_a91448df245e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:43:09.207538+00:00
-- url     : https://prove2.me/theorems/352ed7cd-95a2-4748-94a9-d3d6a4171398
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Order order of integral a91448df245e: P2 M Ground Theory Heights  Heights Inter Regularity Order order of integral a91448df245e
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Order order of integral a91448df245e construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Order order of integral a91448df245e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/OrderOfIntegral.lean#L13-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/OrderOfIntegral.lean#L13-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OrderOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityOrder_order_of_integral_a91448df245e {F : Type*} [Field F] [NumberField F] (S : Subring F)
    (hint : ∀ x ∈ S, IsIntegral ℤ x) (hden : ∀ x : F, ∃ c ∈ S, c ≠ 0 ∧ x * c ∈ S) :
    Module.Finite ℤ S ∧ Module.Free ℤ S ∧ Module.finrank ℤ S = Module.finrank ℚ F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityOrder».«order_of_integral» := P2M_GroundTheory_Heights__Heights_Inter_RegularityOrder_order_of_integral_a91448df245e
