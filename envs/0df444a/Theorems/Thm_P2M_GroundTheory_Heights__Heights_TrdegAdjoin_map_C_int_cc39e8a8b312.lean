-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_C_int_cc39e8a8b312
-- name    : P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_C_int_cc39e8a8b312
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:42.465876+00:00
-- url     : https://prove2.me/theorems/09b39134-8702-4a2b-8d2b-5743367ac341
-- title:
--   P2 M Ground Theory Heights  Heights Trdeg Adjoin map C int cc39e8a8b312: P2 M Ground Theory Heights  Heights Trdeg Adjoin map C int cc39e8a8b312
-- statement:
--   The P2 M Ground Theory Heights  Heights Trdeg Adjoin map C int cc39e8a8b312 construction uses the P2 M Ground Theory Heights  Heights Trdeg Adjoin map C int cc39e8a8b312 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsAlgebraicAdjoinRangeIff.lean#L91-L93

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

theorem P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_C_int_cc39e8a8b312 (φ : MvPolynomial σ ℤ →+* L) (m : ℤ) : φ (C m) = algebraMap ℚ L m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TrdegAdjoin».«map_C_int» := P2M_GroundTheory_Heights__Heights_TrdegAdjoin_map_C_int_cc39e8a8b312
