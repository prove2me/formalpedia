-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_mem_adjoin_f2e6199c8967
-- name    : P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_mem_adjoin_f2e6199c8967
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:16.407589+00:00
-- url     : https://prove2.me/theorems/ac43b081-08b3-49c7-a006-4679584e358a
-- title:
--   P2 M Ground Theory Heights  Heights Trdeg Adjoin map mem adjoin f2e6199c8967: P2 M Ground Theory Heights  Heights Trdeg Adjoin map mem adjoin f2e6199c8967
-- statement:
--   The P2 M Ground Theory Heights  Heights Trdeg Adjoin map mem adjoin f2e6199c8967 construction uses the P2 M Ground Theory Heights  Heights Trdeg Adjoin map mem adjoin f2e6199c8967 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L97-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TrdegAdjoin
open MvPolynomial Algebra Cardinal
attribute [local instance] MvPolynomial.algebraMvPolynomial
noncomputable section
variable {σ : Type} [Fintype σ] {L : Type} [CommRing L] [IsDomain L] [Algebra ℚ L]
omit [Fintype σ] [IsDomain L]

theorem P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_mem_adjoin_f2e6199c8967 (φ : MvPolynomial σ ℤ →+* L) (g : MvPolynomial σ ℤ) :
    φ g ∈ adjoin ℚ (Set.range fun v ↦ φ (X v)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TrdegAdjoin».«map_mem_adjoin» := P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_mem_adjoin_f2e6199c8967
