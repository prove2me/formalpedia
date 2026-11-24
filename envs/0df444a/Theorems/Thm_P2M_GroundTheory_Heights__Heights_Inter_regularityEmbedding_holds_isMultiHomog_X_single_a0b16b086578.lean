-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_isMultiHomog_X_single_a0b16b086578
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_isMultiHomog_X_single_a0b16b086578
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:58.731312+00:00
-- url     : https://prove2.me/theorems/cca391b7-5ed6-4261-9c7d-bf815164d68b
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Embedding holds is Multi Homog X single a0b16b086578: P2 M Ground Theory Heights  Heights Inter regularity Embedding holds is Multi Homog X single
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Embedding holds is Multi Homog X single a0b16b086578 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Embedding holds is Multi Homog X single a0b16b086578 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L27-L38

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
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_isMultiHomog_X_single_a0b16b086578 [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityEmbedding_holds».«isMultiHomog_X_single» := P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_isMultiHomog_X_single_a0b16b086578
