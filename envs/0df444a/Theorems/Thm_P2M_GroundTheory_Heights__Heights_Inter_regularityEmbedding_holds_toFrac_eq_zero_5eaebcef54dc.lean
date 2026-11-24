-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_toFrac_eq_zero_5eaebcef54dc
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_toFrac_eq_zero_5eaebcef54dc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:46.19788+00:00
-- url     : https://prove2.me/theorems/d8d3e45b-35cf-427b-866c-3a382abe0948
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Embedding holds to Frac eq zero 5eaebcef54dc: P2 M Ground Theory Heights  Heights Inter regularity Embedding holds to Frac eq zero 5eaebcef54dc
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Embedding holds to Frac eq zero 5eaebcef54dc construction uses the P2 M Ground Theory Heights  Heights Inter regularity Embedding holds to Frac eq zero 5eaebcef54dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_toFrac_eq_zero_5eaebcef54dc {P : Ideal (MRing ι)} [P.IsPrime] {f : MRing ι} : toFrac P f = 0 ↔ f ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityEmbedding_holds».«toFrac_eq_zero» := P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_toFrac_eq_zero_5eaebcef54dc
